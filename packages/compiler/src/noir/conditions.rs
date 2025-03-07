use super::utils::indent;
use itertools::Itertools;
use std::collections::BTreeSet;

#[derive(Debug, Clone)]
pub struct StateMatch {
    single: usize,         // the single state
    match_vec: Vec<usize>, // all of the states to & with the single state
    s: bool,               // whether single is s or s_next
}

/**
 * Get the final states that can cause the regex match to be accepted or rejected
 *
 */
pub fn get_final_states_predicate(accept_state_ids: &Vec<usize>) -> String {
    accept_state_ids
        .iter()
        .map(|id| format!("(s == {id})"))
        .collect_vec()
        .join(" | ")
}

/**
 * Get the exact end state that a running match should recognize as the end of a match span
 */
pub fn get_end_states_predicate(accept_state_ids: &Vec<usize>) -> String {
    match accept_state_ids.len() == 1 {
        true => format!(
            "(s == {}) & (s_next == {})",
            accept_state_ids[0], accept_state_ids[0]
        ),
        false => format!(
            "(s == {}) & (s_next == {})",
            accept_state_ids[0], accept_state_ids[1]
        ),
    }
}

pub fn get_end_range_predicate(accept_state_ids: &Vec<usize>) -> String {
    accept_state_ids
        .iter()
        .map(|id| format!("(s_next == {})", id))
        .join(" | ")
}

pub fn get_substring_range_predicates(
    substr_ranges: &Vec<BTreeSet<(usize, usize)>>,
) -> (String, String) {
    let substr_functions = substr_ranges
        .iter()
        .enumerate()
        .map(|(index, range)| make_substring_transition_predicate_functions(range, index))
        .join("");

    let substr_cases = (0..substr_ranges.len())
        .map(|i| {
            let range_gate = format!("let range_{i} = range_predicates[0][i];");
            let substr_range_check =
                format!("let substr_check_{i} = substring_{i}_range_check(s, s_next, range_{i});");
            format!(
                r#"
{range_gate}
{substr_range_check}
        "#
            )
        })
        .join("");
    let (composite_check, substring_range_check_target) = match substr_ranges.len() {
        1 => ("".to_string(), "substr_check_0".to_string()),
        _ => {
            let range_cases = (0..substr_ranges.len())
                .map(|i| format!("substr_check_{}", i))
                .join(" * ");
            let composite_check = format!("let composit_check = {};", range_cases);
            (composite_check.to_string(), "composit_check".to_string())
        }
    };
    let range_predicates = indent(
        &format!(
            r#"
{substr_cases}
{composite_check}
let substring_range_check = {substring_range_check_target};
assert_eq(substring_range_check, 0, "substr array ranges wrong");
    "#
        ),
        2,
    );
    (substr_functions, range_predicates)
}

pub fn substring_extraction_conditions(
    substr_ranges: &Vec<BTreeSet<(usize, usize)>>,
    accept_state_ids: &Vec<usize>,
) -> String {
    // 1. SUBSTRING MATCH/ SEQUENCE CONSTURCITON CONDITIONS //
    let mut first_condition = true;
    let mut sequence_conditions = substr_ranges
        .iter()
        .map(|range_set| {
            // Combine the range conditions into a single line using `|` operator
            let range_conditions = range_set
                .iter()
                .map(|(range_start, range_end)| {
                    format!("(s == {range_start}) & (s_next == {range_end})")
                })
                .collect::<Vec<_>>()
                .join(" | ");

            // For the first condition, use `if`, for others, use `else if`
            let (start_part, start_index) = if first_condition {
                first_condition = false;
                let start_index_text = indent(
                    &format!(
                        r#"
if (consecutive_substr == 0) {{
    current_substring.index = i;
}};"#
                    ),
                    1,
                );
                ("if", start_index_text)
            } else {
                ("else if", format!(""))
            };

            // The body of the condition handling substring creation/updating
            format!(
                r#"
{start_part} ({range_conditions}) {{
    {start_index}
    current_substring.length += 1;
    consecutive_substr = 1; 
}}"#
            )
        })
        .collect::<Vec<_>>()
        .join("\n");

    // 2. JOIN WITH FINAL CONDITIONS  //
    let end_states_predicate = get_end_states_predicate(accept_state_ids);
    let substring_conditions = format!(
        r#"
{sequence_conditions} else if ((consecutive_substr == 1) & (s_next == 0)) {{
    current_substring = Sequence::default();
    full_match = Sequence::default();
    substrings = BoundedVec::new();
    consecutive_substr = 0;
}} else if {end_states_predicate} {{
    full_match.length = i - full_match.index + 1;
    complete = true;
}} else if (consecutive_substr == 1) {{
    // The substring is done so "save" it
    substrings.push(current_substring);
    // reset the substring holder for next use
    current_substring = Sequence::default();
    consecutive_substr = 0;
}}"#
    );

    indent(&substring_conditions, 2)
}

/**
 * Determines the combination of (s, s_next) with minimal boolean comparisons to elimitate gates
 *
 * @param states- the s -> s_next pairs for a substring match
 * @param index - the index of the substring match
 * @return the optimize state matches
 */
pub fn make_substring_transition_predicate_functions(
    states: &BTreeSet<(usize, usize)>,
    index: usize,
) -> String {
    use std::collections::{HashMap, HashSet};

    // Create maps for forward and reverse connections
    let mut s_to_next: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut next_to_s: HashMap<usize, Vec<usize>> = HashMap::new();

    for &(s, next) in states {
        s_to_next.entry(s).or_default().push(next);
        next_to_s.entry(next).or_default().push(s);
    }

    // Helper function to get sorted unique values
    let get_unique_sorted = |v: &Vec<usize>| -> Vec<usize> {
        let mut unique: Vec<usize> = v.iter().copied().collect();
        unique.sort_unstable();
        unique.dedup();
        unique
    };

    let mut result = Vec::new();
    let mut covered = HashSet::new();

    // First pass: Find nodes that have multiple outgoing edges
    for (&num, matches_found) in &s_to_next {
        let matches = get_unique_sorted(matches_found);
        if matches.len() > 1 {
            result.push(StateMatch {
                single: num,
                match_vec: matches.clone(),
                s: true,
            });
            for &m in &matches {
                covered.insert((num, m));
            }
        }
    }

    // Second pass: Find remaining edges that need to be covered
    let uncovered = states
        .iter()
        .filter(|&&(s, next)| !covered.contains(&(s, next)))
        .collect::<Vec<_>>();

    // Group remaining by destination
    let mut dest_groups: HashMap<usize, Vec<usize>> = HashMap::new();
    for &(s, next) in &uncovered {
        dest_groups.entry(*next).or_default().push(*s);
    }

    // Add any groups with multiple sources
    for (dest, sources) in dest_groups {
        let mut sources = sources;
        sources.sort_unstable();
        result.push(StateMatch {
            single: dest,
            match_vec: sources,
            s: false,
        });
    }

    // Sort results by single value
    result.sort_by_key(|sm| sm.single);

    let cases = result
        .iter()
        .enumerate()
        .map(|(idx, case)| {
            let (single_label, matches_label) = match case.s {
                true => ("s", "s_next"),
                false => ("s_next", "s"),
            };

            let safety_gap = 0x100usize.pow(idx as u32 + 1);
            let single_case = format!("({single_label} - {}) * 0x{:x})", case.single, safety_gap);
            let multi_match = case
                .match_vec
                .iter()
                .map(|m| format!("({matches_label} - {})", m))
                .join(" * ");
            format!("let case_{idx} = ({single_case} + ({multi_match});")
        })
        .join("\n\t");
    let range_match = match result.len() {
        1 => "range_gate * case_0".to_string(),
        _ => {
            let match_str = (0..result.len()).map(|i| format!("case_{}", i)).join(" * ");
            format!("let char_match = {};\n\trange_gate * char_match", match_str)
        }
    };
    let function = format!(
        r#"
fn substring_{index}_range_check(s: Field, s_next: Field, range_gate: Field) -> Field {{
    {cases}
    {range_match}
}}
    "#
    );
    function
}

/**
 * Either force a check of a final condition, or simply define it and return the bool
 * @dev essentially only used to export regex match conditions
 */
pub fn force_match_condition(
    force_match: bool,
    condition: String,
    return_type: Option<String>,
) -> (String, String, String) {
    // determine the return type and statement to return
    let (return_type_str, return_statement_str) = match return_type.is_some() {
        true => match force_match {
            true => (
                format!("-> {}", return_type.unwrap()),
                String::from("substrings"),
            ),
            false => (
                format!("-> ({}, bool)", return_type.unwrap()),
                String::from("(substrings, matched)"),
            ),
        },
        false => match force_match {
            true => (String::from(""), String::from("")),
            false => (String::from("-> bool"), String::from("matched")),
        },
    };

    let match_statement_str = match force_match {
        true => format!(
            r#"
    assert({condition}, "Match not found");
            "#
        ),
        false => format!(
            r#"
    let matched: bool = {condition};
            "#
        ),
    };
    (return_type_str, return_statement_str, match_statement_str)
}

pub fn make_index_range_predicates(num_substrings: usize) -> String {
    let index_sequences = (0..num_substrings)
        .map(|i| format!("get_index_sequence::<N>(substrings.get_unchecked({i}))"))
        .join(",\n\t");
    indent(
        &format!(
            r#"
let range_predicates = [
    {index_sequences}       
];
    "#
        ),
        1,
    )
}

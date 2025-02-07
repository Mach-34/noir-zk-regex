use std::{
    collections::{BTreeSet, HashSet}, fmt::format, fs::File, io::Write, iter::FromIterator, path::Path
};

use comptime::{FieldElement, SparseArray};
use itertools::Itertools;

use crate::structs::RegexAndDFA;

const ACCEPT_STATE_ID: &str = "accept";
const BYTE_SIZE: u32 = 256; // u8 size

pub fn gen_noir_fn(
    regex_and_dfa: &RegexAndDFA,
    path: &Path,
    gen_substrs: bool,
    sparse_array: Option<bool>,
) -> Result<(), std::io::Error> {
    println!("{}", regex_and_dfa.dfa);
    let use_sparse = sparse_array.unwrap_or(false);
    let noir_fn = to_noir_fn(regex_and_dfa, gen_substrs, use_sparse);
    let mut file = File::create(path)?;
    file.write_all(noir_fn.as_bytes())?;
    file.flush()?;
    Ok(())
}

/// Generates Noir code based on the DFA and whether a substring should be extracted.
///
/// # Arguments
///
/// * `regex_and_dfa` - The `RegexAndDFA` struct containing the regex pattern and DFA.
/// * `gen_substrs` - A boolean indicating whether to generate substrings.
///
/// # Returns
///
/// A `String` that contains the Noir code
fn to_noir_fn(regex_and_dfa: &RegexAndDFA, gen_substrs: bool, sparse_array: bool) -> String {
    // Multiple accepting states are not supported
    // This is a vector nonetheless, to support an extra accepting state we'll use
    // to allow any character occurrences after the original accepting state
    let mut accept_state_ids: Vec<usize> = {
        let accept_states = regex_and_dfa
            .dfa
            .states
            .iter()
            .filter(|s| s.state_type == ACCEPT_STATE_ID)
            .map(|s| s.state_id)
            .collect_vec();
        assert!(
            accept_states.len() == 1,
            "there should be exactly 1 accept state"
        );
        accept_states
    };

    // curr_state + char_code -> next_state
    let mut rows: Vec<(usize, u8, usize)> = vec![];

    // $ support
    // In case that there is no end_anchor, we add an additional accepting state to which any
    // character occurence after the accepting state will go.
    // This needs to be a new state, otherwise substring extraction won't work correctly
    if !regex_and_dfa.has_end_anchor {
        let original_accept_id = accept_state_ids.get(0).unwrap().clone();
        // Create a new highest state
        let extra_accept_id = regex_and_dfa
            .dfa
            .states
            .iter()
            .max_by_key(|state| state.state_id)
            .map(|state| state.state_id)
            .unwrap()
            + 1;
        accept_state_ids.push(extra_accept_id);
        for char_code in 0..=254 {
            rows.push((original_accept_id, char_code, extra_accept_id));
            rows.push((extra_accept_id, char_code, extra_accept_id));
        }
    }

    for state in regex_and_dfa.dfa.states.iter() {
        for (&tran_next_state_id, tran) in &state.transitions {
            for &char_code in tran {
                rows.push((state.state_id, char_code, tran_next_state_id));
            }
        }
    }

    let mut table_size = BYTE_SIZE as usize * regex_and_dfa.dfa.states.len();
    if !regex_and_dfa.has_end_anchor {
        table_size += BYTE_SIZE as usize;
    }

    // handle conditional use of sparse array
    let mut table_str = String::new();
    if !sparse_array {
        let mut lut_body = String::new();
        for (curr_state_id, char_code, next_state_id) in rows {
            lut_body += &format!(
                "table[{curr_state_id} * {BYTE_SIZE} + {char_code}] = {next_state_id};\n",
            );
        }
        lut_body = indent(&lut_body, 1);

        table_str = format!(
            r#"
global table: [Field; {table_size}] = comptime {{ make_lookup_table() }};

comptime fn make_lookup_table() -> [Field; {table_size}] {{
    let mut table = [0; {table_size}];
    {lut_body}
    table
}}

        "#
        );
    } else {
        let mut keys: Vec<FieldElement> = Vec::new();
        let mut values: Vec<FieldElement> = Vec::new();
        for (curr_state_id, char_code, next_state_id) in rows {
            keys.push(FieldElement::from(
                curr_state_id * BYTE_SIZE as usize + char_code as usize,
            ));
            values.push(FieldElement::from(next_state_id));
        }

        let sparse_array: SparseArray<FieldElement> =
            SparseArray::create(&keys, &values, FieldElement::from(table_size));

        table_str = format!(
            r#"
global table: {sparse_str}

            "#,
            sparse_str = sparse_array.to_noir_string(None)
        );
    }

    // make sparse array in comptime

    // let sparse_array_str = sparse_array.to_noir_string(None);

    // substring_ranges contains the transitions that belong to the substring
    let substr_ranges: &Vec<BTreeSet<(usize, usize)>> = &regex_and_dfa.substrings.substring_ranges;
    // Note: substring_boundaries is only filled if the substring info is coming from decomposed setting
    //  and will be empty in the raw setting (using json file for substr transitions). This is why substring_ranges is used here

    let final_states_condition_body = accept_state_ids
        .iter()
        .map(|id| format!("(s == {id})"))
        .collect_vec()
        .join(" | ");
    let end_states_condition_body = format!("(s == {}) & (s_next == {})", accept_state_ids[0], accept_state_ids[1]);
    let finished_condition_body = format!("(s == {}) & (s_next == {})", accept_state_ids[1], accept_state_ids[1]);
    // If substrings have to be extracted, the function returns a vector of BoundedVec
    // otherwise there is no return type
    let all_cases = {
        let mut cases = substr_ranges.iter().map(|range_set| {
            range_set
                .iter()
                .map(|(range_start, range_end)| {
                    indent(&format!("(s == {range_start}) & (s_next == {range_end}),"), 3)
                })
                .collect::<Vec<_>>()
                .join("\n")
        }).collect::<Vec<_>>().join("\n");
        cases = format!(
            "{cases}\n{accept_state}\n{finished_state}",
            accept_state = format!("{},", indent(&end_states_condition_body, 3)),
            finished_state = indent(&finished_condition_body, 3)
        );
        format!("[\n{}\n\t\t];", cases)
    };

    let substr_length = regex_and_dfa.substrings.substring_ranges.len();

      // Constrain substring

      let start_end_index_params = if substr_length > 1 {"start_indices: [u32; NUM_SUBSTRINGS],\n\tend_indices: [u32; NUM_SUBSTRINGS]"} else { "start: u32,\n\tend: u32" };

      let regex_match_constrained_start_end_vars = if substr_length > 1 { "start_indices, end_indices" } else { "start, end" };

      let regex_match_constrained_range_check = if substr_length > 1 {format!("i >= start_indices[0] & i <= end_indices[{substr_length}]")} else {format!("i >= start & i <= end")};

      let regex_match_unconstrained_return_type =  if substr_length > 1 { format!("(BoundedVec<BoundedVec<Field, N>, {substr_length}>, [u32; {substr_length}], [u32; {substr_length}])") } else {format!("(BoundedVec<BoundedVec<Field, N>, {substr_length}>, u32, u32)")};

      let regex_match_unconstrained_indice_array_definitions = if substr_length > 1 { format!("let mut start_indices: [u32; {substr_length}] = [0; {substr_length}];\n\tlet mut end_indices: [u32; {substr_length}] = [0; {substr_length}];") } else { format!("") };

      let regex_match_unconstrained_substr_index_definition = if substr_length > 1 { format!("let mut substr_index = 0;")} else { format!("") };

      let regex_match_unconstrained_indice_array_assignment = if substr_length > 1 { format!("start_indices[substr_index] = start_index;\n\tend_indices[substr_index] = end_index;\n\tsubstr_index += 1;")} else { format!("") };

      let regex_match_unconstrained_return = if substr_length > 1 {"start_indices, end_indices"} else {"start_index, end_index"};

      let single_substring_extraction = if substr_length > 1 { "" } else { "let substring = substrings.get_unchecked(0);\n" };

      let multiple_substring_outer_loop_open = if substr_length > 1 { format!("
  for j in 0..NUM_SUBSTRINGS {{
      let substring = substrings.get_unchecked((j));
      let start = start_indices[j];
      let end = end_indices[j];") } else { format!("") };

      let multiple_substring_outer_loop_close = if substr_length > 1 {"\n}"} else {""};
      let substring_plurality = if substr_length > 1 {"s"} else {""};

      let constrain_substring_static_function_body = format!("
      let mut substr_index = 0;
      for j in 0..INPUT_LEN {{
          let substr_char = substring.get_unchecked(substr_index);
          let input_char = input[j];
          if (j >= start) & (j < end - 1) {{
              assert(substr_char as u8 == input_char);
              substr_index += 1;
          }}
      }}");

    let fn_body = if gen_substrs {
        let mut first_condition = true;

        let mut conditions = substr_ranges
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
                    let start_index_text = format!("\tif (consecutive_substr == 0) {{
        start_index = i;
    }};\n");
                    ("if", start_index_text)
                } else {
                    ("else if", format!(""))
                };


                // The body of the condition handling substring creation/updating
                format!(
                    "{start_part} ({range_conditions}) {{
    {start_index}
    current_substring.push(temp);
    consecutive_substr = 1;   
}}"
                )
            })
            .collect::<Vec<_>>()
            .join("\n");

        // Add the final else if for resetting the consecutive_substr
        let final_conditions = format!(
            "{conditions} else if ((consecutive_substr == 1) & (s_next == 0)) {{
    current_substring = BoundedVec::new();
    substrings = BoundedVec::new();
    consecutive_substr = 0;
    start_index = 0;
    end_index = 0;
}} else if {end_states_condition_body} {{
    end_index = i;
    complete = true;
    break;
}} else if (consecutive_substr == 1) {{
    // The substring is done so \"save\" it
    substrings.push(current_substring);
    // reset the substring holder for next use
    current_substring = BoundedVec::new();
    consecutive_substr = 0;
    {regex_match_unconstrained_indice_array_assignment}
}}"
        );

        conditions = indent(&final_conditions, 2); // Indent twice to align with the for loop's body

        format!(
            r#"
{table_str}

pub fn constrain_substrings<let INPUT_LEN: u32, let NUM_SUBSTRINGS: u32>(
    input: [u8; INPUT_LEN], 
    substrings: BoundedVec<BoundedVec<Field, INPUT_LEN>, NUM_SUBSTRINGS>, 
    {start_end_index_params}
) {{
    {single_substring_extraction}// constrain substring{substring_plurality} {multiple_substring_outer_loop_open}{constrain_substring_static_function_body}{multiple_substring_outer_loop_close}
}}

pub fn regex_match<let N: u32>(input: [u8; N]) -> BoundedVec<BoundedVec<Field, N>, {substr_length}> {{
    let (substrings, {regex_match_constrained_start_end_vars}) = unsafe {{ __regex_match(input) }};

    // constrain extracted substrings
    constrain_substrings::<N, {substr_length}>(input, substrings, {regex_match_constrained_start_end_vars});
    
    // "Previous" state
    let mut s: Field = 0;
    s = {table_access_255};
    // "Next"/upcoming state
    let mut s_next: Field = 0;

    // check the match
    for i in 0..N {{
        let temp = input[i] as Field;
        s_next = {table_access_s_next};
        let potential_s_next = {table_access_s_next_temp};
        if s_next == 0 {{
            s = 0;
            s_next = potential_s_next;
        }}
        std::as_witness(s_next);

        let range = {regex_match_constrained_range_check};
        let cases = {all_cases}
        // idk why have to say == true
        let found = cases.any(|case|  case == true | range == false );
        s = s_next;
        assert(found, "no match");
    }}
    // check final state
    assert({final_states_condition_body}, f"no match: {{s}}");

    substrings
}}

pub unconstrained fn __regex_match<let N: u32>(input: [u8; N]) -> {regex_match_unconstrained_return_type} {{
    // regex: {regex_pattern}
    let mut substrings: BoundedVec<BoundedVec<Field, N>, {substr_length}> = BoundedVec::new();
    {regex_match_unconstrained_indice_array_definitions}

    // "Previous" state
    let mut s: Field = 0;
    s = {table_access_255};
    // "Next"/upcoming state
    let mut s_next: Field = 0;

    let mut consecutive_substr = 0;
    let mut current_substring = BoundedVec::new();
    let mut start_index = 0;
    let mut end_index = 0;
    let mut complete = false;
    {regex_match_unconstrained_substr_index_definition}

    for i in 0..input.len() {{
        let temp = input[i] as Field;
        let mut reset = false;
        s_next = {table_access_s_next};
        let potential_s_next = {table_access_s_next_temp};
        if s_next == 0 {{
            reset = true;
            s = 0;
            s_next = potential_s_next;
        }}
        // If a substring was in the making, but the state was reset
        // we disregard previous progress because apparently it is invalid
        if (reset & (consecutive_substr == 1)) {{
            current_substring = BoundedVec::new();
            consecutive_substr = 0;
        }}
        // Fill up substrings
{conditions}
        s = s_next;
    }}
    assert({final_states_condition_body}, f"no match: {{s}}");
    // Add pending substring that hasn't been added
    if consecutive_substr == 1 {{
        substrings.push(current_substring);
    }}
    (substrings, {regex_match_unconstrained_return})
}}"#,
            regex_pattern = regex_and_dfa
                .regex_pattern
                .replace('\n', "\\n")
                .replace('\r', "\\r"),
            table_access_255 = access_table("255", sparse_array),
            table_access_s_next = access_table("s * 256 + temp", sparse_array),
            table_access_s_next_temp = access_table("temp", sparse_array),
        )
    } else {
        format!(
            r#"
{table_str}
pub fn regex_match<let N: u32>(input: [u8; N]) {{
    // regex: {regex_pattern}
    let mut s = 0;
    s = {table_access_255};
    for i in 0..input.len() {{
        let s_idx = s * {BYTE_SIZE} + input[i] as Field;
        std::as_witness(s_idx);
        s = {table_access_s_idx};
    }}
    assert({final_states_condition_body}, f"no match: {{s}}");
}}"#,
            regex_pattern = regex_and_dfa
                .regex_pattern
                .replace('\n', "\\n")
                .replace('\r', "\\r"),
            table_access_255 = access_table("255", sparse_array),
            table_access_s_idx = access_table("s_idx", sparse_array),
        )
    };

    format!(
        r#"
        {fn_body}
    "#
    )
    .trim()
    .to_owned()
}

/// Indents each line of the given string by a specified number of levels.
/// Each level adds four spaces to the beginning of non-whitespace lines.
fn indent(s: &str, level: usize) -> String {
    let indent_str = "    ".repeat(level);
    s.split("\n")
        .map(|s| {
            if s.trim().is_empty() {
                s.to_owned()
            } else {
                format!("{}{}", indent_str, s)
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Access table by array index or sparse API index
fn access_table(s: &str, sparse: bool) -> String {
    match sparse {
        true => format!("table.get({})", s),
        false => format!("table[{}]", s),
    }
}

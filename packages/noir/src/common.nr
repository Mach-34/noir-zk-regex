/// BYTE SEQUENCE POINTER ///
use dep::sort::sort_advanced;

/// A lookup table that is used to determine if the lookup result from a regex table is 0
/// (note: a bit cheaper than `x != 0`)
pub(crate) global S_IS_ZERO: [Field; 40] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
];

pub struct Sequence {
    index: u32,
    length: u32,
    end: u32,
}

/// Helper method for `get_index_sequence`
unconstrained fn __get_index_sequence<let N: u32>(start: u32, end: u32) -> [Field; N] {
    let mut r: [Field; N] = [0; N];
    for i in 0..N {
        r[i] = ((i >= start) & (i < end)) as Field;
    }
    r
}

/// Returns a size-N array of `Field` elements, `result`, where:
///     1. If `i >= start < end`, result[i] = 1`
///     2. Else, result[i] = 0`
/// This method is much cheaper than testing `start <= i < end` for each value of `i`
/// Cost: 3.333 * N gates
pub(crate) fn get_index_sequence<let N: u32>(start: u32, end: u32) -> [Field; N] {
    // Safety: get the result array and then constrain the fact that it is correct
    let result = unsafe { __get_index_sequence(start, end) };

    assert(end < N, "invalid range");

    // Ok what checks are we applying to validate `result` is accurate?
    // We track the following quantities:
    // 1: `flip_count` = number of times `result[i+1] != result[i]`
    //      note: `flip_count` is initialized to `result[0]`, so if `start == 0`, `flip_count == 1`
    // 2: `flag_count` = number of elements of `result` that are 1
    // 3: `start_idx` = if `result[i] = 0` and `result[i+1] = 1`, `start_idx += i`
    // 4: `result[i]` is boolean
    // Next, we apply the following conditions:
    // 1: `flip_count <= 2` i.e. we can go `0->1`, `0->1->0` or `1->0` or every element can be `0` or `1`
    // 2: `start_idx = start`
    //      `flip_count <= 2` ensures that we only ever have 1 transition from 0->1.
    //       Combined with this check, the first `1` value must occur at `i = start`
    // 3: flag_count = end - start
    //      `flip_count <= 2` ensures we only have ONE consecutive sequence of `1` values
    //      `start_idx = start` ensures the sequence STARTS at `i = start`
    //      `flag_count = end-start` ensures that the sequence continues until `i >= end`
    //
    // FINAL ADJUSTMENT
    // We only apply the above checks if `end > start`
    // If `end <= start` we ensure every value of `result[i]` is 0
    let mut flip_count = result[0];
    let mut start_idx: Field = 0;
    let mut flag_count: Field = 0;
    for i in 0..N - 1 {
        assert_eq(result[i] * result[i], result[i]);
        flip_count += (result[i] + result[i + 1] + result[i] * result[i + 1] * 2);
        std::as_witness(flip_count);

        start_idx += (1 - result[i]) * result[i + 1] * i as Field;
        flag_count += result[i];
    }
    assert_eq(result[N - 1] * result[N - 1], result[N - 1]);
    flag_count += result[N - 1];

    let valid_range = (end > start) as Field;
    let flag_check = (flag_count - (end as Field - start as Field)) * valid_range;
    assert_eq(flag_check, 0);
    let start_check = (start_idx - start as Field) * valid_range;
    assert_eq(start_check, 0);

    // There is likely a more efficient way of checking this but it's like 10 gates out of 25,000 for a regex parse so meh.
    let flip_check_valid_case =
        valid_range * (1 - (((flip_count == 0) | (flip_count == 1) | (flip_count == 2)) as Field));
    let flip_check_invalid_case = (1 - valid_range) * flip_count; // if valid_range = 0, flip_count = 0;
    assert_eq(flip_check_valid_case, 0);
    assert_eq(flip_check_invalid_case, 0);
    result
}

impl Sequence {
    pub fn new(index: u32, length: u32) -> Self {
        Self { index, length, end: index + length }
    }

    pub fn default() -> Self {
        Self { index: 0, length: 0, end: 0 }
    }

    pub fn initialized(self) -> bool {
        self.length > 0
    }

    pub fn index(self) -> u32 {
        self.index
    }

    pub fn length(self) -> u32 {
        self.length
    }

    pub fn end(self) -> u32 {
        self.end
    }

    pub fn in_range(self, index: u32) -> bool {
        // if indexend == 0, index < self.end implicitly returns false if uninitialized
        index >= self.index & index < self.end
    }
}

/// SUBSTRING CAPTURE EXTRACTION ///

/**
 * Extracts all substrings from a pattern match
 * @dev not super optimal - all substrings will be assumed to be of the length of longest substring.
 *      often this will be the size of the input. Use at discretion.
 * 
 * @param input - the input array to extract from
 * @param sequences - the sequences to extract from the input
 * @returns the extracted substrings
 */
pub fn extract_all_substrings<let INPUT_LENGTH: u32, let NUM_SUBSTRINGS: u32, let MAX_SUBSTRING_LENGTH: u32>(
    input: [u8; INPUT_LENGTH],
    sequences: BoundedVec<Sequence, NUM_SUBSTRINGS>,
) -> BoundedVec<BoundedVec<u8, MAX_SUBSTRING_LENGTH>, NUM_SUBSTRINGS> {
    {
        let mut substrings: BoundedVec<BoundedVec<u8, MAX_SUBSTRING_LENGTH>, NUM_SUBSTRINGS> =
            BoundedVec::new();
        for i in 0..NUM_SUBSTRINGS {
            {
                let substring = sequences.get_unchecked(i);
                let mut extracted_substring = extract_substring(substring, input);
                let mut len = substrings.len() + 1;
                if i >= sequences.len() {
                    {
                        extracted_substring = BoundedVec::new();
                        len = substrings.len();
                    }
                }
                substrings.len = len;
                substrings.storage[i] = extracted_substring;
            }
        }
        substrings
    }
}

/**
 * Optimized algorithm for extracting a subsequence from an input array
 * 
 * @param substring_sequence - the sequence to extract from the input
 * @param input - the input array to extract from
 * @returns the extracted subsequence
 */
pub fn extract_substring<let INPUT_LENGTH: u32, let MAX_SUBSTRING_LENGTH: u32>(
    substring_sequence: Sequence,
    input: [u8; INPUT_LENGTH],
) -> BoundedVec<u8, MAX_SUBSTRING_LENGTH> {
    let mut substring: BoundedVec<u8, MAX_SUBSTRING_LENGTH> =
        unsafe { __extract_substring(substring_sequence, input) };
    assert(substring_sequence.length == substring.len(), "length mismatch");
    for i in 0..MAX_SUBSTRING_LENGTH {
        // hack for index to never exceed array bounds
        // must be constrained to be true when matching is required to prevent 0's passing when shouldn't
        // @dev while this adds constraints in worse case it can be more efficient if MAX_SUBSTRING_LENGTH < INPUT_LENGTH
        let input_range_check = substring_sequence.index + i < INPUT_LENGTH;
        let index = (substring_sequence.index + i) as Field * input_range_check as Field;

        // range where input should match substring
        let sequence_range_check = i >= substring_sequence.length;
        // constrain array construction if in range
        let expected_byte = input[index];
        let byte = substring.get_unchecked(i);
        let matched = (expected_byte as Field == byte as Field);
        assert(matched | sequence_range_check, "incorrect substring construction");
    }
    substring
}

/**
 * Unconstrained helper to build the extracted substring
 * @dev must be checked by extract_substring to constrain construction of substring
 * 
 * @param substring_sequence - the sequence to extract from the input
 * @param input - the input array to extract from
 * @returns the extracted subsequence
 */
unconstrained fn __extract_substring<let INPUT_LENGTH: u32, let MAX_SUBSTRING_LENGTH: u32>(
    substring_sequence: Sequence,
    input: [u8; INPUT_LENGTH],
) -> BoundedVec<u8, MAX_SUBSTRING_LENGTH> {
    let mut substring: BoundedVec<u8, MAX_SUBSTRING_LENGTH> = BoundedVec::new();
    for i in 0..substring_sequence.length {
        let byte = input[substring_sequence.index + i];
        substring.push(byte);
    }
    substring
}

/// SUBSTRING CAPTURE INPUT MASKING ///

/**
 * Masks input to only reveal public captures defined in the regex
 *
 * @param substring_sequences - the sequences to mask from the input
 * @param input - the input array to mask
 * @returns the input masked to only reveal public captures defined in the regex
 */
pub fn mask_input<let INPUT_LENGTH: u32, let MAX_SUBSTRING_LENGTH: u32>(
    substring_sequences: BoundedVec<Sequence, MAX_SUBSTRING_LENGTH>,
    input: [u8; INPUT_LENGTH],
) -> [u8; INPUT_LENGTH] {
    let masked: [u8; INPUT_LENGTH] = unsafe { __mask_input(substring_sequences, input) };
    for i in 0..INPUT_LENGTH {
        let any_in_range =
            substring_sequences.storage().any(|sequence: Sequence| sequence.in_range(i));
        let expected_byte = input[i] as Field * any_in_range as Field;
        assert(masked[i] as Field == expected_byte, "Incorrect masking");
    }
    masked
}

/**
 * Unconstrained helper to mask input
 * @dev SHOULD NOT BE CALLED BY ANYTHING EXCEPT `mask_input`
 * 
 * @param substring_sequences - the sequences to mask from the input
 * @param input - the input array to mask
 * @returns the input masked to only reveal public captures defined in the regex
 */
unconstrained fn __mask_input<let INPUT_LENGTH: u32, let MAX_SUBSTRING_LENGTH: u32>(
    substring_sequences: BoundedVec<Sequence, MAX_SUBSTRING_LENGTH>,
    input: [u8; INPUT_LENGTH],
) -> [u8; INPUT_LENGTH] {
    let mut masked_input: [u8; INPUT_LENGTH] = [0; INPUT_LENGTH];
    for i in 0..substring_sequences.len() {
        let sequence = substring_sequences.get_unchecked(i);
        for j in sequence.index..sequence.end() {
            masked_input[j] = input[j];
        }
    }
    masked_input
}

/// VECTOR REVERSAL ///

pub fn reverse_vec<let N: u32>(input: BoundedVec<u8, N>) -> BoundedVec<u8, N> {
    let mut reversed = unsafe { __reverse_vec(input) };
    for i in 0..N {
        let in_range = (i < reversed.len()) as Field;
        // if in range choose opposite index, otherwise choose same index to check 0's
        // yeah I know this is ugly show me a more efficient version and I'll use it
        let index = (
            ((input.len() as Field) - (i as Field * in_range) - 1) * in_range as Field
                + (i as Field * (1 - in_range))
        ) as Field;
        let expected_byte = input.get_unchecked(index as u32) as Field * in_range as Field;
        let byte = reversed.get_unchecked(i) as Field;
        assert(byte == expected_byte, "Incorrect reverse");
    }
    reversed
}

unconstrained fn __reverse_vec<let N: u32>(input: BoundedVec<u8, N>) -> BoundedVec<u8, N> {
    let mut reversed: BoundedVec<u8, N> = BoundedVec::new();
    for i in 0..input.len() {
        reversed.push(input.get(input.len() - i - 1));
    }
    reversed
}


/// Helper fn for `extract_s_params_from_table`
unconstrained fn __extract_s_params_from_table(input: Field) -> (Field, Field) {
    let x = input as u16;
    let lo = x & 63;
    let hi = x >> 6;
    (lo as Field, hi as Field)
}

/// Given a lookup table that encodes 2 6-bit values as a 12-bit Field element,
/// return the low and high 6-bit values
pub(crate) fn extract_s_params_from_table(input: Field) -> (Field, Field) {
    // Safety: extract the 6-bit slices and then validate they are correctly formed
    let (s_next, potential_next_s) = unsafe { __extract_s_params_from_table(input) };
    s_next.assert_max_bit_size::<6>();
    potential_next_s.assert_max_bit_size::<6>();
    assert_eq(s_next + potential_next_s * 64, input);
    (s_next, potential_next_s)
}

unconstrained fn __sort_field_as_u32(lhs: Field, rhs: Field) -> bool {
    //  lhs.lt(rhs)
    lhs as u32 <= rhs as u32
}
pub struct SparseArray<let N: u32, T> {
    pub keys: [Field; N + 2],
    pub values: [T; N + 3],
    pub  maximum: Field, // can be up to 2^32
}

fn assert_sorted(lhs: Field, rhs: Field) {
    let result = (rhs - lhs - 1);
    result.assert_max_bit_size::<32>();
}

/// Note: excisting SparseArray impl has a small bug, local impl until fixed
pub impl<let N: u32, T> SparseArray<N, T>
where
    T: std::default::Default,
{

    /**
     * @brief construct a SparseArray
     **/
    pub fn create(_keys: [Field; N], _values: [T; N], size: Field) -> Self {
        let _maximum = size - 1;
        let mut r: Self =
            SparseArray { keys: [0; N + 2], values: [T::default(); N + 3], maximum: _maximum };

        // for any valid index, we want to ensure the following is satified:
        // self.keys[X] <= index <= self.keys[X+1]
        // this requires us to sort hte keys, and insert a startpoint and endpoint
        let sorted_keys = sort_advanced(_keys, __sort_field_as_u32, assert_sorted);

        // insert start and endpoints
        r.keys[0] = 0;
        for i in 0..N {
            r.keys[i + 1] = sorted_keys.sorted[i];
        }
        r.keys[N + 1] = _maximum;

        // populate values based on the sorted keys
        // note: self.keys[i] maps to self.values[i+1]
        // self.values[0] does not map to any key. we use it to store the default empty value,
        // which is returned when `get(idx)` is called and `idx` does not exist in `self.keys`
        for i in 0..N {
            // if (sorted_keys.sorted[i] == 0x0d)
            // {
            //     let x = sorted_keys.sort_indices[i];
            //     let y = _values[sorted_keys.sort_indices[i]];
            //     println(f"i = {i}, sort indices = {x}, value? = {y}");
            //     assert(x == -1);
            // }
            // THIS IS THE BUG: the commented line was the original line
            r.values[sorted_keys.sort_indices[i] + 2] = _values[i];
        //    r.values[i + 2] = _values[sorted_keys.sort_indices[i]];
        }
        // insert values that map to our key start and endpoints
        // if _keys[0] = 0 then values[0] must equal _values[0], so some conditional logic is required
        // (same for _keys[N-1])
        let mut initial_value = T::default();
        if (_keys[0] == 0) {
            initial_value = _values[0];
        }
        let mut final_value = T::default();
        if (_keys[N - 1] == _maximum) {
            final_value = _values[N - 1];
        }
        r.values[1] = initial_value;
        r.values[N + 2] = final_value;

        // perform boundary checks!
        // the maximum size of the sparse array is 2^32
        // we need to check that every element in `self.keys` is less than 2^32
        // because `self.keys` is sorted, we can simply validate that
        // sorted_keys.sorted[0] < 2^32
        // sorted_keys.sorted[N-1] < maximum
        sorted_keys.sorted[0].assert_max_bit_size::<32>();
        _maximum.assert_max_bit_size::<32>();
        (_maximum - sorted_keys.sorted[N - 1]).assert_max_bit_size::<32>();
        r
    }

    /**
     * @brief determine whether `target` is present in `self.keys`
     * @details if `found == false`, `self.keys[found_index] < target < self.keys[found_index + 1]`
     **/
    unconstrained fn search_for_key(self, target: Field) -> (Field, Field) {
        let mut found = false;
        let mut found_index = 0;
        let mut previous_less_than_or_equal_to_target = false;
        for i in 0..N + 2 {
            // if target = 0xffffffff we need to be able to add 1 here, so use u64
            let current_less_than_or_equal_to_target = self.keys[i] as u64 <= target as u64;
            if (self.keys[i] == target) {
                found = true;
                found_index = i as Field;
                break;
            }
            if (previous_less_than_or_equal_to_target & !current_less_than_or_equal_to_target) {
                found_index = i as Field - 1;
                break;
            }
            previous_less_than_or_equal_to_target = current_less_than_or_equal_to_target;
        }
        (found as Field, found_index)
    }

    /**
     * @brief return element `idx` from the sparse array
     * @details cost is 14.5 gates per lookup
     **/
    pub fn get(self, idx: Field) -> T {
        let (found, found_index) = unsafe { self.search_for_key(idx) };
        // bool check. 0.25 gates cheaper than a raw `bool` type. need to fix at some point
        assert(found * found == found);

        // OK! So we have the following cases to check
        // 1. if `found` then `self.keys[found_index] == idx`
        // 2. if `!found` then `self.keys[found_index] < idx < self.keys[found_index + 1]
        // how do we simplify these checks?
        // case 1 can be converted to `self.keys[found_index] <= idx <= self.keys[found_index]
        // case 2 can be modified to  `self.keys[found_index] + 1 <= idx <= self.keys[found_index + 1] - 1
        // combine the two into the following single statement:
        // `self.keys[found_index] + 1 - found <= idx <= self.keys[found_index + 1 - found] - 1 + found
        let lhs = self.keys[found_index];
        let rhs = self.keys[found_index + 1 - found];
        let lhs_condition = idx - lhs - 1 + found;
        let rhs_condition = rhs - 1 + found - idx;
        lhs_condition.assert_max_bit_size::<32>();
        rhs_condition.assert_max_bit_size::<32>();

        // self.keys[i] maps to self.values[i+1]
        // however...if we did not find a non-sparse entry, we want to return self.values[0] (the default value)
        let value_index = (found_index + 1) * found;
        self.values[value_index]
    }
}

/// This method takes a regex table and returns the size of the equivalent sparse table
pub(crate) unconstrained fn get_num_sparse_entries<let N: u32>(
    table: [Field; N],
) -> u32 {

    let mut keys: BoundedVec<Field, N> = BoundedVec::new();
    let mut values: BoundedVec<Field, N> = BoundedVec::new();


    let mut small_keys: BoundedVec<Field, 256> = BoundedVec::new();
    let mut small_values: BoundedVec<Field, 256> = BoundedVec::new();

    let mut max_value: u32 = 0;
    for i in 0..N {
        if (table[i] as u32 > max_value)
        {
            max_value = table[i] as u32;
        }
        if (table[i] != 0) {
            keys.push(i as Field);
            values.push(table[i]);

            if (i < 256)
            {
                small_keys.push(i as Field);
                small_values.push(table[i]);
            }
        }
    }

    for i in 0..small_keys.len() {
        let target_value = small_values.get(i) * 256;
        for j in 0..max_value {
            let target_key = j as Field * 256 + small_keys.get(i);
            let mut found_key: bool = false;
            for k in 0..keys.len() {
                if (keys.get(k) == target_key) {
                    values.set(k, values.get(k) + target_value);
                    found_key = true;
                    break;
                }
            }
            if (!found_key) {
                keys.push(target_key);
                values.push(target_value);
            }
        }
    }

    let new_num_entries = keys.len();
    new_num_entries
}

/// This method takes a regex table and, given knowledge of the size of the sparse table (NewN), returns the sparse table
/// Note the sparse table values utilize a dual encoding
/// The low 6 bits are the equivalent of `table[s * 256 + index]` from the main regex algorithm
/// The high 6 bits are the equivalent of `table[index]`
/// This prevents us from needing to do 2 SparseArray lookups per iteration (which are expensive at 14.5 gates per lookup)
pub(crate) unconstrained fn convert_to_sparse_packed_array<let N: u32, let NewN: u32>(
    table: [Field; N],
    max_size: u32,
) -> SparseArray<NewN, Field> {
    let mut small_keys: BoundedVec<Field, 256> = BoundedVec::new();
    let mut small_values: BoundedVec<Field, 256> = BoundedVec::new();
    let mut keys: BoundedVec<Field, N> = BoundedVec::new();
    let mut values: BoundedVec<Field, N> = BoundedVec::new();


    let mut max_value: u32 = 0;
    for i in 0..N {
        if (table[i] as u32 > max_value)
        {
            max_value = table[i] as u32;
        }
        if (table[i] != 0) {
            keys.push(i as Field);
            values.push(table[i]);

            if (i < 256)
            {
                small_keys.push(i as Field);
                small_values.push(table[i]);
            }
        }
    }

    for i in 0..small_keys.len() {
        let target_value = small_values.get(i) * 256;
        for j in 0..max_value {
            let target_key = j as Field * 256 + small_keys.get(i);
            let mut found_key: bool = false;
            for k in 0..keys.len() {
                if (keys.get(k) == target_key) {
                    values.set(k, values.get(k) + target_value);
                    found_key = true;
                    break;
                }
            }
            if (!found_key) {
                keys.push(target_key);
                values.push(target_value);
            }
        }
    }

    let new_num_entries = keys.len();
    assert(new_num_entries == NewN);

    let mut new_keys: [Field; NewN] = [0; NewN];
    let mut new_values: [Field; NewN] = [0; NewN];

    for i in 0..NewN {
        new_keys[i] = keys.get(i);
        new_values[i] = values.get(i);
    }

    let r: SparseArray<NewN, Field> = SparseArray::create(new_keys, new_values, max_size as Field);

    println(f"global sparse_table: SparseArray<{NewN}, Field> = {r}");
    r
}

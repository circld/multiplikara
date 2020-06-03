/// To get the most out of this assignment, your program should restrict itself to multiplying only
/// pairs of single-digit numbers. You can implement the grade-school algorithm if you want, but to
/// get the most out of the assignment you'll want to implement recursive integer multiplication
/// and/or Karatsuba's algorithm.
///
/// Assignment asks for product of:
/// - 3141592653589793238462643383279502884197169399375105820974944592
/// - 2718281828459045235360287471352662497757247093699959574966967627
use clap::{App, Arg};
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::fmt;
use std::iter::Iterator;
use std::ops::{Add, Mul};

fn main() {
    let matches = App::new("c1w1")
        .version("0.1")
        .about("Coursera Algorithms Nanodegree: Course 1 Week 1 programming assignment")
        .arg(
            Arg::with_name("numbers")
                .help("Numbers to multiply together (requires > 1).")
                .required(true)
                .min_values(2),
        )
        .get_matches();

    let mut numbers: Vec<NumberStr> = matches
        .values_of("numbers")
        .expect("ERROR")
        .map(NumberStr::new)
        .collect();

    // TODO there has to be a better way, but `NumberStr::Mul` takes ownership so refactoring to
    // take references seems tricky.
    let first = numbers.remove(0);
    let second = numbers.remove(1);
    println!("{:?}, {:?}", first, second);
    println!("{}", first * second);
}

#[derive(Debug, PartialEq)]
struct Digit {
    character: char,
    digit: u32,
}

impl Digit {
    fn new(character: char) -> Digit {
        Digit {
            character,
            digit: character.to_digit(10).unwrap(),
        }
    }
}

impl From<u32> for Digit {
    fn from(digit: u32) -> Digit {
        let digit_str = digit.to_string();
        assert!(digit_str.len() == 1);
        let character = digit_str.chars().last().unwrap();
        Digit { character, digit }
    }
}

#[derive(Debug, PartialEq)]
struct NumberStr {
    value: VecDeque<Digit>,
    positive: bool,
}

impl NumberStr {
    fn new(value: &str) -> Self {
        let mut characters = value.chars().peekable();
        let positive = match characters.peek() {
            Some(&v) => v != '-',
            None => false,
        };
        if !positive {
            // if None branch above (iterator exhausted), this returns None
            characters.next();
        }

        // consume leading zeroes
        // n.b., `take_while` consumes first non-match :facepalm:
        while let Some(&d) = characters.peek() {
            if d != '0' {
                break;
            }
            characters.next();
        }

        // no digits left!
        if characters.peek().is_none() {
            let mut v = VecDeque::new();
            v.push_back(Digit::new('0'));
            NumberStr {
                value: v,
                positive: false,
            }
        } else {
            NumberStr {
                value: characters.map(Digit::new).collect(),
                positive,
            }
        }
    }

    fn len(&self) -> usize {
        self.value.len()
    }

    /// Create a `NumberStr` instance from a `VecDeque` and an indicator whether positive
    fn make(value: VecDeque<Digit>, positive: bool) -> Self {
        let value_str: String = value.iter().map(|d| d.character).collect();
        if !positive {
            let mut v = String::from("-");
            v.push_str(&value_str);
            NumberStr::new(&v)
        } else {
            NumberStr::new(&value_str)
        }
    }

    /// Order pair of `NumberStr` instances based on length in ascending order
    fn order<'a>(&'a self, other: &'a Self) -> (&'a Self, &'a Self) {
        if self.len() > other.len() {
            (other, self)
        } else {
            (self, other)
        }
    }

    fn split_at(mut self, idx: usize) -> (Self, Self) {
        let positive = self.positive;
        let new_vd = self.value.split_off(idx);
        self.value.shrink_to_fit();
        (self, NumberStr::make(new_vd, positive))
    }

    fn flip_sign(mut self) -> Self {
        self.positive = !self.positive;
        self
    }
}

impl Clone for NumberStr {
    fn clone(&self) -> Self {
        Self::new(&self.to_string())
    }
}

impl From<&str> for NumberStr {
    fn from(s: &str) -> Self {
        Self::new(s)
    }
}

impl Into<String> for NumberStr {
    fn into(self) -> String {
        // available bc implemented `Display`
        self.to_string()
    }
}

impl fmt::Display for NumberStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let base: String = self.value.iter().map(|d| d.character).collect();
        let to_print = if self.positive {
            base
        } else {
            let mut to_print = String::from("-");
            to_print.push_str(&base);
            to_print
        };
        write!(f, "{}", to_print,)
    }
}

impl PartialOrd for NumberStr {
    /// Attempt to match on length, but if same length, then compare digits left-to-right.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.positive && !other.positive {
            return Some(Ordering::Greater);
        }
        if !self.positive && other.positive {
            return Some(Ordering::Less);
        }
        let invert = !self.positive && !other.positive;
        match self.len().cmp(&other.len()) {
            Ordering::Greater => {
                if !invert {
                    Some(Ordering::Greater)
                } else {
                    Some(Ordering::Less)
                }
            }
            Ordering::Less => {
                if !invert {
                    Some(Ordering::Less)
                } else {
                    Some(Ordering::Greater)
                }
            }
            Ordering::Equal => {
                for (a, b) in self.value.iter().zip(other.value.iter()) {
                    match a.digit.cmp(&b.digit) {
                        Ordering::Greater => {
                            return if !invert {
                                Some(Ordering::Greater)
                            } else {
                                Some(Ordering::Less)
                            }
                        }
                        Ordering::Less => {
                            return if !invert {
                                Some(Ordering::Less)
                            } else {
                                Some(Ordering::Greater)
                            }
                        }
                        Ordering::Equal => continue,
                    }
                }
                Some(Ordering::Equal)
            }
        }
    }
}

impl Add for NumberStr {
    type Output = Self;

    /// Add two numbers represented as strings and return a string.
    ///
    /// This has the advantage of being able to operate numbers too large for built-in arithmetic
    /// operations
    fn add(self, other: Self) -> Self {
        let invert = if self.positive != other.positive {
            -1
        } else {
            1
        };

        let (smaller, larger) = self.order(&other);

        let mut value: VecDeque<Digit> = VecDeque::new();
        let mut x;
        let mut carry = 0;
        let mut large_iter = larger.value.iter();
        let mut small_iter = smaller.value.iter();

        while let Some(digit_l) = large_iter.next_back() {
            if let Some(digit_s) = small_iter.next_back() {
                x = digit_l.digit as i32 + invert * (digit_s.digit as i32 + carry);
            } else {
                x = digit_l.digit as i32 + invert * carry;
            }
            // used carry value above
            carry = 0;

            // new carry
            if x > 9 {
                carry = 1;
                x -= 10;
            }
            if x < 0 {
                carry = 1;
                x += 10;
            }

            value.push_front(Digit::from(x as u32));
        }
        if carry > 0 {
            value.push_front(Digit::new('1'));
        }

        NumberStr::make(value, larger.positive)
    }
}

#[allow(suspicious_arithmetic_impl)]
impl Mul for NumberStr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        // FIXME: base case
        // if one is len 1, then split will yield...???
        println!("{:?}, {:?}", self, rhs);

        if self.len() == 1 && rhs.len() == 1 {
            return NumberStr::new(
                &(self.value.front().unwrap().digit * rhs.value.front().unwrap().digit).to_string(),
            );
        }

        let mid = midpoint(self.len(), rhs.len());
        let mut b: VecDeque<Digit> = VecDeque::new();
        let mut b2: VecDeque<Digit> = VecDeque::new();
        for i in 0..(2 * mid) {
            b2.push_front(Digit::new('0'));
            if i < mid {
                b.push_front(Digit::new('0'));
            }
        }

        // calculate a0, a1, b0, b1
        let (len_s, len_r) = (self.len(), rhs.len());
        let (a0, a1) = self.split_at(len_s - mid);
        let (b0, b1) = rhs.split_at(len_r - mid);

        // calculate z0, z1, z2
        let mut z0 = a0.clone() * b0.clone();
        let mut z1 = a1.clone() * b1.clone();
        let z2 =
            (a0 + a1) * (b0 + b1) + z0.clone() + z0.clone().flip_sign() + z1.clone().flip_sign();

        // add base
        z0.value.append(&mut b2);
        z1.value.append(&mut b);

        z0 + z1 + z2
    }
}

fn midpoint(len1: usize, len2: usize) -> usize {
    let longer = if len1 > len2 { len1 } else { len2 };
    let shorter = if len1 < len2 { len1 } else { len2 };

    let theta = (longer as f32 - shorter as f32 + 1.) / longer as f32;
    let ratio = 2f32.powf(theta - 1.);
    let shorter_f = shorter as f32;
    let max_f = (shorter - 1) as f32;

    (shorter_f * ratio).min(max_f).floor() as usize
}

// TODO: turn into a method on a struct `NumberStr`
// TODO: implement karatsuba using `NumberStr` abstraction
// want multiply to work even when `a` and `b` are of different lengths
fn multiply(a: &str, b: &str) -> String {
    let debug_msg = format!("a = {}, b = {}", a, b);
    // println!("{}", &debug_msg);

    // determine base
    // for now, hardcode base 10^3, and if either input < 10^3, just use built-in multiplication
    if a.replace("-", "").len() < 4 || b.replace("-", "").len() < 4 {
        return (a.parse::<i128>().unwrap() * b.parse::<i128>().unwrap()).to_string();
    }
    let b_pow = 3;
    let base = 10i128.pow(b_pow);

    // convert inputs into: a0, a1, b0, b1
    let (a0, a1) = a.split_at(a.len() - b_pow as usize);
    let (b0, b1) = b.split_at(b.len() - b_pow as usize);

    // calculate z0, z1, and with these, z'
    let z0 = multiply(a0, b0).parse::<i128>().expect(&debug_msg);
    let z1 = multiply(a1, b1).parse::<i128>().expect(&debug_msg);
    let z = multiply(
        &(a0.parse::<i128>().unwrap() + a1.parse::<i128>().expect(&debug_msg)).to_string(),
        &(b0.parse::<i128>().unwrap() + b1.parse::<i128>().expect(&debug_msg)).to_string(),
    )
    .parse::<i128>()
    .expect(&debug_msg)
        - z0
        - z1;

    // calculate result
    let mut z0_mut = z0.to_string();
    z0_mut.push_str(&base.pow(2).to_string().replace("1", ""));

    let mut z_mut = z.to_string();
    z_mut.push_str(&base.to_string().replace("1", ""));

    println!("{}, {}, {}", &z0_mut, &z_mut, z1);
    (NumberStr::new(&z0_mut) + NumberStr::new(&z_mut) + NumberStr::new(&z1.to_string())).into()
}

#[cfg(test)]
mod test {
    use super::{midpoint, Digit, NumberStr, VecDeque};

    #[test]
    fn new_numberstr_test() {
        assert_eq!("-1234", NumberStr::new("-1234").to_string());
    }

    #[test]
    fn new_numberstr_empty_string_test() {
        assert_eq!(NumberStr::new("0"), NumberStr::new(""));
    }

    #[test]
    fn new_number_str_from_collection_test() {
        let mut v: VecDeque<Digit> = VecDeque::new();
        v.push_back(Digit::new('1'));
        v.push_back(Digit::new('2'));
        v.push_back(Digit::new('3'));
        v.push_back(Digit::new('4'));
        assert_eq!("-1234", NumberStr::make(v, false).to_string());
    }

    #[test]
    fn cmp_positive_larger_test() {
        assert!(NumberStr::new("1000") > NumberStr::new("53"));
    }

    #[test]
    fn cmp_positive_smaller_same_len_test() {
        assert!(NumberStr::new("8111") < NumberStr::new("8112"));
    }

    #[test]
    fn cmp_smaller_one_negative_test() {
        assert!(NumberStr::new("-50") < NumberStr::new("8"));
    }

    #[test]
    fn cmp_both_negative_larger_test() {
        assert!(NumberStr::new("-50") > NumberStr::new("-800"));
    }

    #[test]
    fn cmp_both_negative_larger_same_len_test() {
        assert!(NumberStr::new("-505") > NumberStr::new("-800"));
    }

    #[test]
    fn add_single_digit_with_carry_test() {
        assert_eq!(
            NumberStr::new("10").to_string(),
            (NumberStr::new("4") + NumberStr::new("6")).to_string()
        )
    }

    #[test]
    fn add_different_digit_counts_test() {
        assert_eq!(
            NumberStr::new("8895").to_string(),
            (NumberStr::new("6") + NumberStr::new("8889")).to_string()
        );
    }

    #[test]
    fn add_two_negative_test() {
        assert_eq!(
            NumberStr::new("-21").to_string(),
            (NumberStr::new("-5") + NumberStr::new("-16")).to_string()
        );
    }

    #[test]
    fn add_mixed_sign_larger_positive_test() {
        assert_eq!(
            NumberStr::new("5").to_string(),
            (NumberStr::new("-122") + NumberStr::new("127")).to_string()
        );
    }

    #[test]
    fn add_mixed_sign_larger_negative_test() {
        assert_eq!(
            NumberStr::new("-5").to_string(),
            (NumberStr::new("122") + NumberStr::new("-127")).to_string()
        );
    }

    #[test]
    fn add_oom_numbers_test() {
        assert_eq!(
            NumberStr::new("5859874482048838473822930854632165381954416493075065395941912219")
                .to_string(),
            (NumberStr::new("3141592653589793238462643383279502884197169399375105820974944592")
                + NumberStr::new(
                    "2718281828459045235360287471352662497757247093699959574966967627"
                ))
            .to_string()
        )
    }

    #[test]
    fn multiply_small_test() {
        assert_eq!(
            "1024",
            (NumberStr::new("64") * NumberStr::new("16")).to_string()
        )
    }

    #[test]
    fn multiply_large_test() {
        assert_eq!(
            "97421969088",
            (NumberStr::new("123456") * NumberStr::new("789123")).to_string()
        )
    }

    #[test]
    fn multiply_one_negative_test() {
        assert!(NumberStr::new("1335") * NumberStr::new("-884") < NumberStr::new("0"))
    }

    #[test]
    fn multiply_two_negative_test() {
        assert!(NumberStr::new("-13335496") * NumberStr::new("-999988") > NumberStr::new("0"))
    }

    #[test]
    fn midpoint_same_test() {
        assert_eq!(3, midpoint(6, 6));
    }

    #[test]
    fn midpoint_smaller_first_test() {
        assert_eq!(6, midpoint(8, 26));
    }

    #[test]
    fn midpoint_larger_first() {
        assert_eq!(7, midpoint(200, 8));
    }

    #[test]
    fn split_at_test() {
        assert_eq!(
            (NumberStr::new("123"), NumberStr::new("456")),
            NumberStr::new("123456").split_at(3)
        );
    }

    #[test]
    fn flip_sign_pos_to_neg_test() {
        assert_eq!(NumberStr::new("-123"), NumberStr::new("123").flip_sign());
    }

    #[test]
    fn flip_sign_neg_to_pos_test() {
        assert_eq!(NumberStr::new("123"), NumberStr::new("-123").flip_sign());
    }
}

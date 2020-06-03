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

    let numbers: Vec<&str> = matches.values_of("numbers").expect("ERROR").collect();
    println!("{}", multiply(&numbers[0], &numbers[1]));
    // println!("{}", multiply("123456", "789123"));
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
    fn new(value: &str) -> NumberStr {
        let mut characters = value.chars().peekable();
        let positive = characters.peek().unwrap() != &'-';
        if !positive {
            characters.next();
        }
        NumberStr {
            value: characters.map(Digit::new).collect(),
            positive,
        }
    }

    fn len(&self) -> usize {
        self.value.len()
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
        let base = self.value.iter().map(|d| d.character).collect::<String>();
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
    fn partial_cmp(&self, other: &NumberStr) -> Option<Ordering> {
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
        // TODO: implement adding of negative numbers //
        // if larger is negative, tack '-' on at the end
        // if only one is negative, larger + -1 * smaller
        let larger = if self > other { &self } else { &other };
        let smaller = if self > other { &other } else { &self };

        let mut value: VecDeque<Digit> = VecDeque::new();
        let mut x;
        let mut carry = 0;
        let mut large_iter = larger.value.iter();
        let mut small_iter = smaller.value.iter();

        while let Some(digit_l) = large_iter.next_back() {
            if let Some(digit_s) = small_iter.next_back() {
                x = digit_l.digit + digit_s.digit + carry;
            } else {
                x = digit_l.digit + carry;
            }
            // used carry value above
            carry = 0;

            // new carry
            if x > 9 {
                carry = 1;
                x -= 10;
            }

            value.push_front(Digit::from(x));
        }
        if carry > 0 {
            value.push_front(Digit::new('1'));
        }

        NumberStr {
            value,
            positive: true,
        }
    }
}

impl Mul for NumberStr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        // TODO implement this after completing `add`
        unimplemented!()
    }
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
    use super::{multiply, NumberStr};

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
    fn multiply_small_test() {
        assert_eq!(String::from("1024"), multiply("64", "16"))
    }

    #[test]
    fn multiply_large_test() {
        assert_eq!("97421969088", multiply("123456", "789123"))
    }

    #[test]
    fn multiply_one_negative_test() {
        assert!(multiply("1335", "-884").parse::<i32>().unwrap() < 0)
    }

    #[test]
    fn multiply_two_negative_test() {
        assert!(multiply("-13335496", "-999988").parse::<i128>().unwrap() > 0)
    }

    #[test]
    fn add_single_digit_with_carry_test() {
        assert_eq!(
            NumberStr::new("10"),
            NumberStr::new("4") + NumberStr::new("6")
        )
    }

    #[test]
    fn add_different_digit_counts_test() {
        assert_eq!(
            NumberStr::new("8895"),
            NumberStr::new("6") + NumberStr::new("8889")
        );
    }

    #[test]
    fn add_two_negative_test() {
        assert_eq!(
            NumberStr::new("-21"),
            NumberStr::new("-5") + NumberStr::new("-16")
        );
    }

    #[test]
    fn add_mixed_sign_larger_positive_test() {
        assert_eq!(
            NumberStr::new("5"),
            NumberStr::new("-122") + NumberStr::new("127")
        );
    }

    #[test]
    fn add_mixed_sign_larger_negative_test() {
        assert_eq!(
            NumberStr::new("-5"),
            NumberStr::new("122") + NumberStr::new("-127")
        );
    }

    #[test]
    fn add_oom_numbers_test() {
        assert_eq!(
            NumberStr::new("5859874482048838473822930854632165381954416493075065395941912219"),
            NumberStr::new("3141592653589793238462643383279502884197169399375105820974944592")
                + NumberStr::new(
                    "2718281828459045235360287471352662497757247093699959574966967627"
                )
        )
    }
}

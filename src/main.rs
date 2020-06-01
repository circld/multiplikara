/// To get the most out of this assignment, your program should restrict itself to multiplying only
/// pairs of single-digit numbers. You can implement the grade-school algorithm if you want, but to
/// get the most out of the assignment you'll want to implement recursive integer multiplication
/// and/or Karatsuba's algorithm.
///
/// Assignment asks for product of:
/// - 3141592653589793238462643383279502884197169399375105820974944592
/// - 2718281828459045235360287471352662497757247093699959574966967627
use clap::{App, Arg};
use std::collections::VecDeque;
use std::iter::Iterator;

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
    add(&add(&z0_mut, &z_mut), &z1.to_string())
}

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

/// Add two numbers represented as strings and return a string.
///
/// This has the advantage of being able to operate numbers too large for built-in arithmetic
/// operations
fn add(a: &str, b: &str) -> String {
    // TODO: implement adding of negative numbers //
    // if larger is negative, tack '-' on at the end
    // if only one is negative, larger + -1 * smaller

    let larger = if a.len() > b.len() { a } else { b };
    let smaller = if a.len() > b.len() { b } else { a };

    let mut digits_l = larger.chars().map(Digit::new);
    let mut digits_s = smaller.chars().map(Digit::new);

    let mut carry = 0;
    let mut summed: VecDeque<char> = VecDeque::new();
    let mut x_digit: Digit;

    while let Some(c_l) = digits_l.next_back() {
        #[allow(unused_assignments)]
        let mut x = 0;

        if let Some(c_s) = digits_s.next_back() {
            x = c_l.digit + c_s.digit + carry;
        } else {
            x = c_l.digit + carry;
        }
        // already used carry above
        carry = 0;

        if x >= 10 {
            carry = 1;
            x -= 10;
        }
        x_digit = Digit::from(x);
        summed.push_front(x_digit.character);
    }

    // if we still have value in carry, append to number
    if carry > 0 {
        summed.push_front('1');
    }

    summed.iter().collect()
}

#[cfg(test)]
mod test {
    use super::{add, multiply};

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
        assert_eq!("10", add("4", "6"))
    }

    #[test]
    fn add_different_digit_counts_test() {
        assert_eq!("8895", add("6", "8889"))
    }

    #[test]
    fn add_two_negative_test() {
        assert_eq!("-21", add("-5", "-16"));
    }

    #[test]
    fn add_mixed_sign_larger_positive_test() {
        assert_eq!("5", add("-122", "127"));
    }

    #[test]
    fn add_mixed_sign_larger_negative_test() {
        assert_eq!("-5", add("122", "-127"));
    }

    #[test]
    fn add_oom_numbers_test() {
        assert_eq!(
            "5859874482048838473822930854632165381954416493075065395941912219",
            add(
                "3141592653589793238462643383279502884197169399375105820974944592",
                "2718281828459045235360287471352662497757247093699959574966967627"
            )
        )
    }
}

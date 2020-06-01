/// To get the most out of this assignment, your program should restrict itself to multiplying only
/// pairs of single-digit numbers. You can implement the grade-school algorithm if you want, but to
/// get the most out of the assignment you'll want to implement recursive integer multiplication
/// and/or Karatsuba's algorithm.
///
/// Assignment asks for product of:
/// - 3141592653589793238462643383279502884197169399375105820974944592
/// - 2718281828459045235360287471352662497757247093699959574966967627
use clap::{App, Arg};
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
}

// want multiply to work even when `a` and `b` are of different lengths
fn multiply(a: &str, b: &str) -> String {
    // exponentiation: i64::pow (should be method on type)

    // determine base
    // for now, hardcode base 10^3, and if either input < 10^3, just use built-in multiplication
    if a.replace("-", "").len() < 4 || b.replace("-", "").len() < 4 {
        return (a.parse::<i32>().unwrap() * b.parse::<i32>().unwrap()).to_string();
    }
    let b_pow = 3;
    let base = 10i64.pow(b_pow);

    // convert inputs into: a0, a1, b0, b1
    let (a0, a1) = a.split_at(a.len() - b_pow as usize);
    let (b0, b1) = b.split_at(b.len() - b_pow as usize);
    let a0 = a0.parse::<i64>().unwrap();
    let a1 = a1.parse::<i64>().unwrap();
    let b0 = b0.parse::<i64>().unwrap();
    let b1 = b1.parse::<i64>().unwrap();

    // calculate z0, z1, and with these, z'
    let z0 = a0 * b0;
    let z1 = a1 * b1;
    let z = (a0 + a1) * (b0 + b1) - z0 - z1;

    // calculate result
    i64::to_string(&(z0 * base.pow(2) + z * base + z1))
}

#[cfg(test)]
mod test {
    use super::multiply;

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
        assert!(multiply("-13335496", "-999988").parse::<i64>().unwrap() > 0)
    }
}

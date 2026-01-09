use crate::poly::VarIndex;
use num_bigint::BigInt;
use num_traits::Num;
use std::ops::Neg;

pub fn parse_poly(line: &[u8]) -> impl Iterator<Item = (BigInt, Vec<VarIndex>)> {
    PolyParser::new(line)
}

struct PolyParser<'a> {
    line: &'a [u8],
}

impl<'a> PolyParser<'a> {
    fn new(line: &'a [u8]) -> Self {
        Self { line }
    }
}

impl<'a> Iterator for PolyParser<'a> {
    type Item = (BigInt, Vec<VarIndex>);

    fn next(&mut self) -> Option<Self::Item> {
        use State::*;
        let mut state = LookingForSign(0);
        let mut coef: Option<BigInt> = None;
        let mut vars = Vec::with_capacity(16);
        while !self.line.is_empty() {
            state = match state {
                LookingForSign(i) => {
                    // end of line special case
                    if i == self.line.len() {
                        self.line = &[];
                        continue;
                    }
                    match self.line[i] {
                        b'+' => ParsingCoef(Sign::Plus, i + 1, i + 1),
                        b'-' => ParsingCoef(Sign::Minus, i + 1, i + 1),
                        // sometimes there is no sign
                        b'0' | b'1' | b'2' | b'3' | b'4' | b'5' | b'6' | b'7' | b'8' | b'9' => {
                            ParsingCoef(Sign::Plus, i, i + 1)
                        }
                        _ => LookingForSign(i + 1),
                    }
                }
                ParsingCoef(sign, start, i) => {
                    // end of line special case
                    if i == self.line.len() {
                        let s = std::str::from_utf8(&self.line[start..i]).unwrap().trim();
                        self.line = &[];
                        return Some((BigInt::from_str_radix(s, 10).unwrap(), vec![]));
                    }
                    match self.line[i] {
                        // skip whitespace and `[` at the beginning
                        b' ' | b'[' if start == i => ParsingCoef(sign, i + 1, i + 1),
                        b'*' | b']' => {
                            let s = std::str::from_utf8(&self.line[start..i]).unwrap().trim();
                            if sign == Sign::Minus {
                                coef = Some(BigInt::from_str_radix(s, 10).unwrap().neg());
                            } else {
                                coef = Some(BigInt::from_str_radix(s, 10).unwrap());
                            }
                            ParsingVar(i + 1, i + 1)
                        }
                        _ => ParsingCoef(sign, start, i + 1),
                    }
                }
                ParsingVar(start, i) => {
                    // end of line special case
                    if i == self.line.len() {
                        let var: u32 = std::str::from_utf8(&self.line[start..i])
                            .unwrap()
                            .parse()
                            .unwrap();
                        self.line = &[];
                        vars.push(var.into());
                        return Some((coef.unwrap(), vars));
                    }
                    match self.line[i] {
                        b'x' => {
                            debug_assert_eq!(start, i);
                            ParsingVar(i + 1, i + 1)
                        }
                        b'0' | b'1' | b'2' | b'3' | b'4' | b'5' | b'6' | b'7' | b'8' | b'9' => {
                            ParsingVar(start, i + 1)
                        }
                        other => {
                            if start != i {
                                let var: u32 = std::str::from_utf8(&self.line[start..i])
                                    .unwrap()
                                    .parse()
                                    .unwrap();
                                vars.push(var.into());
                            }
                            // there is another var waiting!
                            if other == b'*' {
                                ParsingVar(i + 1, i + 1)
                            } else {
                                // done!
                                self.line = &self.line[i..];
                                return Some((coef.unwrap(), vars));
                            }
                        }
                    }
                }
            }
        }
        None
    }
}

#[derive(Debug, Copy, Clone)]
enum State {
    LookingForSign(usize),
    ParsingCoef(Sign, usize, usize),
    ParsingVar(usize, usize),
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum Sign {
    Minus,
    Plus,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_poly() {
        assert_eq!(
            parse_poly(b"-1*x2817+1*x33").collect::<Vec<_>>(),
            [
                (BigInt::from(-1), vec![2817.into()]),
                (BigInt::from(1), vec![33.into()])
            ]
        );
        assert_eq!(parse_poly(b"+2147483648*x2848+1073741824*x2847+536870912*x2846+268435456*x2845+134217728*x2844+67108864*x2843+33554432*x2842+16777216*x2841").collect::<Vec<_>>(),
                   [(BigInt::from(2147483648u64), vec![2848.into()]),
                       (BigInt::from(1073741824u64), vec![2847.into()]),
                       (BigInt::from(536870912u64), vec![2846.into()]),
                       (BigInt::from(268435456u64), vec![2845.into()]),
                       (BigInt::from(134217728u64), vec![2844.into()]),
                       (BigInt::from(67108864u64), vec![2843.into()]),
                       (BigInt::from(33554432u64), vec![2842.into()]),
                       (BigInt::from(16777216u64), vec![2841.into()]),

                   ]);

        // here there is a `+1` at the end
        assert_eq!(
            parse_poly(b"-1*x663-1*x493+1").collect::<Vec<_>>(),
            [
                (BigInt::from(-1), vec![663.into()]),
                (BigInt::from(-1), vec![493.into()]),
                (BigInt::from(1), vec![])
            ]
        );

        // from `b03_sp-ar-rc_64bit_step`
        assert_eq!(
            parse_poly(b"-2*x65*x2-1*x65*x1").collect::<Vec<_>>(),
            [
                (BigInt::from(-2), vec![65.into(), 2.into()]),
                (BigInt::from(-1), vec![65.into(), 1.into()]),
            ]
        );
    }

    // make sure that we can parse polynoms that are turned into strings using our implementation of Display
    #[test]
    fn test_parse_polynom_display() {
        assert_eq!(
            parse_poly(b"[1*x2817] + [1*x33]").collect::<Vec<_>>(),
            [
                (BigInt::from(1), vec![2817.into()]),
                (BigInt::from(1), vec![33.into()])
            ]
        );

        assert_eq!(
            parse_poly(b"[-1*x2817] + [1*x33]").collect::<Vec<_>>(),
            [
                (BigInt::from(-1), vec![2817.into()]),
                (BigInt::from(1), vec![33.into()])
            ]
        );

        assert_eq!(
            parse_poly(b"[1*x2817] + [ -1 *x33]").collect::<Vec<_>>(),
            [
                (BigInt::from(1), vec![2817.into()]),
                (BigInt::from(-1), vec![33.into()])
            ]
        );

        // parse a monom with empty term
        assert_eq!(
            parse_poly(b"[2*] + [4294967294*x1*x18]").collect::<Vec<_>>(),
            [
                (BigInt::from(2), vec![]),
                (BigInt::from(4294967294u64), vec![1.into(), 18.into()])
            ]
        );
    }
}

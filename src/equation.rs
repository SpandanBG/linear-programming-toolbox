//! This module contains the various methods and function to create and manupulate an equation.
//!
//! An equation is of the following type:
//! `a1x1 + a2x2 + ... + aNxN <= b1`
//!
//! Where `aM` is the `M`th coefficient of the variable `xM`.
//!
//! And the equation if of the type: `lhs <= rhs`
//!
//! # Example
//!
//! ```
//! use lp_toolbox::equation::{EqType, Equation, DVar};
//! 
//! // 4x + 2y = 6
//! let eqn = Equation::new(vec![DVar(4e0, 1), DVar(2e0, 2)], EqType::EQ, 6e0);
//! ```

#[derive(Debug, PartialEq)]
/// Possible equality type in a given equation
pub enum EqType {
    /// Equal (rhs == lhs)
    EQ = 1,

    /// Greater Than (rhs > lhs)
    GT = 2,

    /// Greater Than or Equal To (rhs >= lhs)
    GTE = 3,
    
    /// Less Than (rhs < lhs)
    LT = 4,

    /// Less Than or Equal To (rhs <= lhs)
    LTE = 5
}

#[derive(Debug, PartialEq, Clone)]
/// Represents a variable name (`xM`)
///
/// Each `xM` is represented by the struct `VarM(char, u32)`:
/// - Here the `char` is the character `x`
/// - And the `u32` is the number `M` 
pub struct VarM(pub char, pub u32);

#[derive(Debug)]
/// Represents a decision variable (`aMxM`)
///
/// Each `aMxM` is represented by the struct `DVar(f64, VarM)`:
/// - Here the `f64` is the coefficent `aM`
/// - And the `VarM` is an ID representing `xM`
pub struct DVar(pub f64, pub VarM);

#[derive(Debug)]
/// Represents an equation (`a1x1 + a2x2 + ... + aNxN <= b1`)
pub struct Equation {
    lhs: Vec<DVar>,
    eq_type: EqType,
    rhs: f64
}

#[derive(Debug)]
/// Represents an iterator to the `LHS` to the equation
pub struct EquationIterator<'a> {
    equation: &'a Equation,
    index: usize,
}

impl Equation {
    /// Creates a new Equation
    ///
    /// # Arguments
    ///
    /// * `lhs` - `Vec<DVar>` which describes the LHS of your equation
    /// * `eq_type` - `EqType` which describes the equality type of your equation
    /// * `rhs` - `f64` which describes RHS of your equation
    ///
    /// # Example
    ///
    /// ```
    /// use lp_toolbox::equation::{EqType, Equation, DVar};
    /// 
    /// // 1x + 2y = 3
    /// let eq = Equation::new(vec![DVar(1e0, 1), DVar(2e0, 1)], EqType::EQ, 3e0);
    /// ```
    pub fn new(lhs: Vec<DVar>, eq_type: EqType, rhs: f64) -> Equation {
        return Equation { lhs, rhs, eq_type };
    }

    /// Creates a new EquationIterator which provides an iterator over the `lhs`
    ///
    /// # Example
    ///
    /// ```
    /// use lp_toolbox::equation::{EqType, Equation, DVar};
    ///
    /// // 1x + 2y = 3
    /// let eq = Equation::new(vec![DVar(1e0, 1), DVar(2e0, 2)], EqType::EQ, 3e0);
    /// let mut eq_iter = eq.iter();
    ///
    /// let item = eq_iter.next();
    /// assert_eq!(item.unwrap().0, 1e0);
    /// assert_eq!(item.unwrap().1, 1);
    /// ```
    pub fn iter(&self) -> EquationIterator {
        EquationIterator {
            equation: self,
            index: 0,
        }
    }

    /// RHS getter
    ///
    /// # Example
    ///
    /// ```
    /// use lp_toolbox::equation::{EqType, Equation, DVar};
    ///
    /// // 1x + 2y = 3
    /// let eq = Equation::new(vec![DVar(1e0, 1), DVar(2e0, 2)], EqType::EQ, 3e0);
    ///
    /// let rhs = eq.get_rhs();
    /// assert_eq!(rhs, 3e0);
    /// ```
    pub fn get_rhs(&self) -> f64 {
        return self.rhs;
    }
}

impl<'a> Iterator for EquationIterator<'a> {
    type Item = &'a DVar;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.equation.lhs.len() {
            return None;
        }

        let value = self.equation.lhs.get(self.index);
        self.index += 1;
        return value;
    }
}

#[cfg(test)]
mod equation_tests {
    use super::{DVar, VarM, Equation, EqType};

    #[test]
    fn should_create_basic_equation() {
        let eqn = Equation::new(vec![DVar(2e0, VarM('x', 1))], EqType::LTE, 4e0);

        assert_eq!(eqn.lhs[0].0,  2e0);
        assert_eq!(eqn.lhs[0].1,  VarM('x', 1));
        assert_eq!(eqn.rhs,  4e0);
        assert_eq!(eqn.eq_type, EqType::LTE);
    }
}

#[cfg(test)]
mod equation_iterator_tests {
    use super::{DVar, VarM, Equation, EqType};

    #[test]
    fn should_iter_through_rhs() {
        let eqn = Equation::new(vec![DVar(1e0, VarM('x', 1)), DVar(2e0, VarM('x', 2))], EqType::EQ, 3e0);

        let mut eqn_iter = eqn.iter();

        let item = eqn_iter.next();
        assert_eq!(item.unwrap().0, 1e0);
        assert_eq!(item.unwrap().1, VarM('x', 1));

        let item = eqn_iter.next();
        assert_eq!(item.unwrap().0, 2e0);
        assert_eq!(item.unwrap().1, VarM('x', 2));
    }
}

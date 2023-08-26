//! This feature module contains the algorithm to solve a Maximization and Minimization problem
//! using the Simplex method.

use crate::equation::Equation;

#[derive(Debug, PartialEq)]
/// Possible problem type
pub enum ProblemType {
    MAX = 1,
    MIN = 2,
}

#[derive(Debug)]
/// Represents the simplex table in a single iteration
pub struct SimplexTable {
    iteration_no: u64,
    problem_type: ProblemType,
    c_j: Vec<f64>,
    basic_var: Vec<u64>,
    c_b_i: Vec<f64>,
    entered_basic_var: Vec<u64>,
    solution: Vec<f64>,
    ratio: Vec<f64>,
    z_j: Vec<f64>,
    c_j_minus_z_j: Vec<f64>,
    st_table: Vec<f64>,
    st_height: usize,
    st_width: usize,
}

impl SimplexTable {
    pub fn new(
        problem_type: ProblemType,
        objective_fn: &Equation,
        conditions: &Vec<Equation>,
    ) -> SimplexTable {
        let (c_j, basic_var) = SimplexTable::get_cj_and_basic_vars(objective_fn);
        let (c_b_i, entered_basic_var) =
            SimplexTable::get_cbi_and_entered_basic_vars(&c_j, &basic_var, conditions.len());
        let (solution, ratio) = SimplexTable::get_sols_and_ratios(&conditions);
        let (st_table, st_height, st_width) = SimplexTable::get_soluton_table(&conditions);

        SimplexTable {
            iteration_no: 0,
            problem_type,
            c_j,
            basic_var,
            c_b_i,
            entered_basic_var,
            solution,
            ratio,
            z_j: vec![0e0; st_width],
            c_j_minus_z_j: vec![0e0; st_width],
            st_table,
            st_height,
            st_width,
        }
    }

    fn get_cj_and_basic_vars(objective_fn: &Equation) -> (Vec<f64>, Vec<u64>) {
        let mut c_j = vec![];
        let mut basic_var = vec![];

        for d_var in objective_fn.iter() {
            c_j.push(d_var.0);
            basic_var.push(d_var.1)
        }

        return (c_j, basic_var);
    }

    fn get_cbi_and_entered_basic_vars(
        c_j: &Vec<f64>,
        basic_var: &Vec<u64>,
        no_of_slacks: usize,
    ) -> (Vec<f64>, Vec<u64>) {
        let mut c_b_i = vec![];
        let mut entered_basic_var = vec![];

        let end_idx = c_j.len();
        let start_idx = end_idx - no_of_slacks;

        for i in start_idx..end_idx {
            c_b_i.push(c_j[i]);
            entered_basic_var.push(basic_var[i]);
        }

        return (c_b_i, entered_basic_var);
    }

    fn get_sols_and_ratios(conditions: &Vec<Equation>) -> (Vec<f64>, Vec<f64>) {
        let mut solution = vec![];
        let mut ratio = vec![];

        for cond in conditions.iter() {
            solution.push(cond.get_rhs());
            ratio.push(cond.get_rhs());
        }

        return (solution, ratio);
    }

    fn get_soluton_table(conditions: &Vec<Equation>) -> (Vec<f64>, usize, usize) {
        let mut st_table: Vec<f64> = vec![];
        let st_height = conditions.len();
        for cond in conditions.iter() {
            st_table.extend(cond.iter().map(|dv| dv.0));
        }
        let st_width = st_table.len() / st_height;
        return (st_table, st_height, st_width);
    }
}

#[cfg(test)]
mod simplex_tests {
    use crate::{equation::{Equation, DVar}, constants::EqType};
    use super::{SimplexTable, ProblemType};

    /// Setups the basic maximization problem
    ///
    /// Maximize `12x + 16y = Z`
    /// Subjected to:
    /// - `10x + 12y <= 120`
    /// - `8x + 8y <= 80`
    /// - `x & y >= 0`
    fn setup_max_problem() -> (ProblemType, Equation, Vec<Equation>) {
        // `12x + 16y + 0s1 + 0s2`
        let objective_fn = Equation::new(vec![DVar(12e0, 1), DVar(16e0, 2), DVar(0e0, 3), DVar(0e0, 4)], EqType::EQ, 0e0);

        let subjected_to = vec![
            // `10x + 12y + s1 + 0s2 + 0a1 + 0a2 <= 120`
            Equation::new(vec![DVar(10e0, 1), DVar(12e0, 2), DVar(1e0, 3), DVar(0e0, 4)], EqType::LTE, 120e0),
            // `8x + 8y + 0s1 + s2 + 0a1 + 0a2 <= 80`
            Equation::new(vec![DVar(8e0, 1), DVar(8e0, 2), DVar(0e0, 3), DVar(1e0, 4)], EqType::LTE, 80e0),
        ];

        return (ProblemType::MAX, objective_fn, subjected_to);
    }

    #[test]
    fn should_create_simplex_table() {
        let (problem_type, objective_fn, subjected_to) = setup_max_problem();
        let simplex = SimplexTable::new(problem_type, &objective_fn, &subjected_to);

        assert_eq!(simplex.iteration_no, 0);
        assert_eq!(simplex.problem_type, ProblemType::MAX);
        assert_eq!(simplex.c_j, vec![12e0, 16e0, 0e0, 0e0]);
        assert_eq!(simplex.basic_var, vec![1, 2, 3, 4]);
        assert_eq!(simplex.c_b_i, vec![0e0, 0e0]);
        assert_eq!(simplex.entered_basic_var, vec![3, 4]);
        assert_eq!(simplex.solution, vec![120e0, 80e0]);
        assert_eq!(simplex.ratio, vec![120e0, 80e0]);
        assert_eq!(simplex.z_j, vec![0e0, 0e0, 0e0, 0e0]);
        assert_eq!(simplex.c_j_minus_z_j, vec![0e0, 0e0, 0e0, 0e0]);
        assert_eq!(simplex.st_table, vec![10e0, 12e0, 1e0, 0e0, 8e0, 8e0, 0e0, 1e0]);
        assert_eq!(simplex.st_height, 2);
        assert_eq!(simplex.st_width, 4);
    }
}

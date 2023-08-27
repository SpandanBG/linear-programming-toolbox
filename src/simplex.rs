//! This feature module contains the algorithm to solve a Maximization and Minimization problem
//! using the Simplex method.

use crate::{
    coord::{Coord, NavDir},
    equation::Equation,
};

#[derive(Debug, PartialEq)]
/// Possible problem type
pub enum ProblemType {
    /// Maximization problem
    MAX = 1,

    /// Minimization problem
    MIN = 2,
}

#[derive(Debug)]
/// Represents the simplex table in a single iteration
pub struct SimplexTable {
    /// Iteration number while solving the simplex table
    iteration_no: u64,

    /// Problem type (maximization / minimization problem)
    problem_type: ProblemType,

    /// Cj => Coeff.s of Objective fn (`aM`)
    c_j: Vec<f64>,

    /// Basic Variables => Variales of Objective fn (`xM`)
    basic_var: Vec<u64>,

    /// 
    c_b_i: Vec<f64>,
    entered_basic_var: Vec<u64>,
    solution: Vec<f64>,
    ratio: Vec<f64>,
    z_j: Vec<f64>,
    c_j_minus_z_j: Vec<f64>,
    st_table: Vec<f64>,
    st_key_col: Vec<f64>,
    st_key_row: Vec<f64>,
    st_key_elem: f64,
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
        let solution = SimplexTable::get_sols(&conditions);
        let (st_table, st_height, st_width) = SimplexTable::get_soluton_table(&conditions);

        SimplexTable {
            iteration_no: 0,
            problem_type,
            c_j,
            basic_var,
            c_b_i,
            entered_basic_var,
            solution,
            ratio: vec![0e0; conditions.len()],
            z_j: vec![0e0; st_width],
            c_j_minus_z_j: vec![0e0; st_width],
            st_table,
            st_key_col: vec![0e0; st_height],
            st_key_row: vec![0e0; st_width + 1],
            st_key_elem: 0e0,
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

    fn get_sols(conditions: &Vec<Equation>) -> Vec<f64> {
        let mut solution = vec![];
        for cond in conditions.iter() {
            solution.push(cond.get_rhs());
        }
        return solution;
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

    pub fn next(&mut self) -> bool {
        self.update_z_j();
        let key_col = self.update_c_j_minus_z_j();

        if self.is_solved() {
            return false;
        }

        let key_row = self.update_ratio(key_col);
        self.update_st_key_elem(key_col, key_row);
        self.update_st_key_row(key_row);
        self.update_st_rest(key_row);
        self.update_entries(key_col, key_row);
        self.iteration_no += 1;

        return true;
    }

    fn st_coord(&self, x: usize, y: usize) -> Coord {
        return Coord::new(x, y, self.st_width, self.st_height);
    }

    fn is_solved(&self) -> bool {
        let optimality_fn = match self.problem_type {
            ProblemType::MAX => |&each: &f64| each <= 0e0,
            ProblemType::MIN => |&each: &f64| each >= 0e0,
        };
        return self.c_j_minus_z_j.iter().all(optimality_fn);
    }

    fn update_z_j(&mut self) {
        let st_table_coord = self.st_coord(0, 0);
        for (j, rt_coord) in st_table_coord.iter(NavDir::RIGHT).enumerate() {
            let mut z_j_i = 0e0;
            for (i, dwn_coord) in rt_coord.iter(NavDir::DOWN).enumerate() {
                z_j_i += self.st_table[dwn_coord.to_index()] * self.c_b_i[i];
            }
            self.z_j[j] = z_j_i;
        }
    }

    fn update_c_j_minus_z_j(&mut self) -> usize {
        let mut largest_value = 0e0;
        let mut key_col = 0;
        for i in 0..self.z_j.len() {
            let updated_val = self.c_j[i] - self.z_j[i];
            if updated_val > largest_value {
                largest_value = updated_val;
                key_col = i;
            }
            self.c_j_minus_z_j[i] = updated_val;
        }
        for (i, key_coord) in self.st_coord(key_col, 0).iter(NavDir::DOWN).enumerate() {
            self.st_key_col[i] = self.st_table[key_coord.to_index()];
        }
        return key_col;
    }

    fn update_ratio(&mut self, key_col: usize) -> usize {
        let st_table_coord = self.st_coord(key_col, 0);
        let mut smallest_value = f64::MAX;
        let mut key_row = 0;
        for (i, dwn_coord) in st_table_coord.iter(NavDir::DOWN).enumerate() {
            let updated_value = self.solution[i] / self.st_table[dwn_coord.to_index()];
            if updated_value < smallest_value {
                smallest_value = updated_value;
                key_row = i;
            }
            self.ratio[i] = updated_value;
        }
        for (i, key_coord) in self.st_coord(0, key_row).iter(NavDir::RIGHT).enumerate() {
            self.st_key_row[i] = self.st_table[key_coord.to_index()];
        }
        let last_index = self.st_key_row.len() - 1;
        self.st_key_row[last_index] = self.solution[key_row];
        return key_row;
    }

    fn update_st_key_elem(&mut self, key_col: usize, key_row: usize) {
        self.st_key_elem = self.st_table[self.st_coord(key_col, key_row).to_index()];
    }

    fn update_st_key_row(&mut self, key_row: usize) {
        let row_coord = self.st_coord(0, key_row);
        for rt_coord in row_coord.iter(NavDir::RIGHT) {
            self.st_table[rt_coord.to_index()] /= self.st_key_elem;
        }
        self.solution[key_row] /= self.st_key_elem;
    }

    fn update_st_rest(&mut self, key_row: usize) {
        for dwn_coord in self.st_coord(0, 0).iter(NavDir::DOWN) {
            if dwn_coord.y == key_row {
                continue;
            }

            for rt_coord in dwn_coord.iter(NavDir::RIGHT) {
                let corres_key_col_val = self.st_key_col[rt_coord.y];
                let corres_key_row_val = self.st_key_row[rt_coord.x];
                self.st_table[rt_coord.to_index()] -=
                    (corres_key_col_val * corres_key_row_val) / self.st_key_elem;
            }
        }
        for i in 0..self.solution.len() {
            if i == key_row {
                continue;
            }
            let last_row_idx = self.st_key_row.len() - 1;
            let corres_key_col_val = self.st_key_col[i];
            let corres_key_row_val = self.st_key_row[last_row_idx];
            self.solution[i] -= (corres_key_col_val * corres_key_row_val) / self.st_key_elem;
        }
    }

    fn update_entries(&mut self, key_col: usize, key_row: usize) {
        let new_entering_basic_var = self.basic_var[key_col];
        let new_entering_c_b_i = self.c_j[key_col];
        self.entered_basic_var[key_row] = new_entering_basic_var;
        self.c_b_i[key_row] = new_entering_c_b_i;
    }
}

#[cfg(test)]
mod simplex_tests {
    use super::{ProblemType, SimplexTable};
    use crate::{
        constants::EqType,
        equation::{DVar, Equation},
    };

    /// Setups the basic maximization problem
    ///
    /// Maximize `12x + 16y = Z`
    /// Subjected to:
    /// - `10x + 12y <= 120`
    /// - `8x + 8y <= 80`
    /// - `x & y >= 0`
    fn setup_max_problem() -> (ProblemType, Equation, Vec<Equation>) {
        // `12x + 16y + 0s1 + 0s2`
        let objective_fn = Equation::new(
            vec![DVar(12e0, 1), DVar(16e0, 2), DVar(0e0, 3), DVar(0e0, 4)],
            EqType::EQ,
            0e0,
        );

        let subjected_to = vec![
            // `10x + 20y + s1 + 0s2 + 0a1 + 0a2 <= 120`
            Equation::new(
                vec![DVar(10e0, 1), DVar(20e0, 2), DVar(1e0, 3), DVar(0e0, 4)],
                EqType::LTE,
                120e0,
            ),
            // `8x + 8y + 0s1 + s2 + 0a1 + 0a2 <= 80`
            Equation::new(
                vec![DVar(8e0, 1), DVar(8e0, 2), DVar(0e0, 3), DVar(1e0, 4)],
                EqType::LTE,
                80e0,
            ),
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
        assert_eq!(simplex.ratio, vec![0e0, 0e0]);
        assert_eq!(simplex.z_j, vec![0e0, 0e0, 0e0, 0e0]);
        assert_eq!(simplex.c_j_minus_z_j, vec![0e0, 0e0, 0e0, 0e0]);
        assert_eq!(
            simplex.st_table,
            vec![10e0, 20e0, 1e0, 0e0, 8e0, 8e0, 0e0, 1e0]
        );
        assert_eq!(simplex.st_height, 2);
        assert_eq!(simplex.st_width, 4);
    }

    #[test]
    fn should_solve_simplex_table() {
        let (problem_type, objective_fn, subjected_to) = setup_max_problem();
        let mut simplex = SimplexTable::new(problem_type, &objective_fn, &subjected_to);

        simplex.next();

        assert_eq!(simplex.entered_basic_var, vec![2, 4]);
        assert_eq!(simplex.solution, vec![6e0, 32e0]);

        simplex.next();

        assert_eq!(simplex.entered_basic_var, vec![2, 1]);
        assert_eq!(simplex.solution, vec![2e0, 8e0]);

        assert!(!simplex.next());
    }
}

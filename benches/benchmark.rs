use criterion::{black_box, criterion_group, criterion_main, Criterion};

use lp_toolbox::{
    simplex::{ProblemType, SimplexTable},
    equation::{DVar, VarM, EqType, Equation},
};

fn setup_simplex_max_problem() -> (Equation, Vec<Equation>) {
    // `12x + 16y + 0s1 + 0s2`
    let objective_fn = Equation::new(
        vec![DVar(12e0, VarM('x', 1)), DVar(16e0, VarM('x', 2)), DVar(-0e0, VarM('x', 3)), DVar(-0e0, VarM('x', 4))],
        EqType::EQ,
        0e0,
        );

    let subjected_to = vec![
        // `10x + 20y + s1 + 0s2 <= 120`
        Equation::new(
            vec![DVar(10e0, VarM('x', 1)), DVar(20e0, VarM('x', 2)), DVar(1e0, VarM('x', 3)), DVar(0e0, VarM('x', 4))],
            EqType::LTE,
            120e0,
            ),
            // `8x + 8y + 0s1 + s2 <= 80`
            Equation::new(
                vec![DVar(8e0, VarM('x', 1)), DVar(8e0, VarM('x', 2)), DVar(0e0, VarM('x', 3)), DVar(1e0, VarM('x', 4))],
                EqType::LTE,
                80e0,
                ),
    ];

    return (objective_fn, subjected_to);
}

fn solved_in_simplex(problem_type: ProblemType, objective_fn: &Equation, subjected_to: &Vec<Equation>) {
    let mut simplex = SimplexTable::new(problem_type, objective_fn, subjected_to);
    while simplex.next() {};
}

fn simplex_benchmark(c: &mut Criterion) {
    let (objective_fn, subjected_to) = setup_simplex_max_problem();
    c.bench_function("simplex max problem", |b| b.iter(|| {
        solved_in_simplex(ProblemType::MAX, &objective_fn, &subjected_to)
    }));
}

criterion_group!(benches, simplex_benchmark);
criterion_main!(benches);

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use cyclic::modular;

const BIG_PRIME: u32 = 179424673;

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("big_power", |b| {
        b.iter(|| {
            let num = modular::Modular::<BIG_PRIME>::new(1000000);
            num.pow(1000000)
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);

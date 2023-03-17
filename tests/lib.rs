use std::ops::{Add, Mul, Sub};
use rand::Rng;
use kdtree_rust::{EuclideanDistance, KDTree};

fn nearest<'a,const D:usize,P>(p:&'a [P;D],positions:&'a [[P;D]]) -> &'a [P;D]
    where P: PartialOrd + Mul + Add + Sub + Default,
          &'a [P;D]: EuclideanDistance<&'a [P;D], Output = P> + 'a {
    let s = &positions[0];
    let mut r = s;

    let mut distance = p.euclidean_distance(r);

    for pt in positions.iter().skip(1) {
        let d = p.euclidean_distance(pt);

        if d <= distance {
            r = pt;
            distance = d;
        }
    }

    r
}
#[test]
fn small_2d() {
    const COUNT:usize = 100;

    let mut kdt = KDTree::<2,f64,()>::new();

    let mut rng = rand::thread_rng();

    let mut positions:Vec<[f64;2]> = vec![];

    for _ in 0..COUNT {
        let mut pn = [0f64;2];

        for i in 0..2 {
            let mut p:f64 = rng.gen_range(-100000.0..100000.0);
            let pi:u8 = rng.gen_range(0..10);

            if let Some(last) = positions.last() {
                if pi == 0 {
                    p = last[i];
                }
            }

            pn[i] = p;
        }

        positions.push(pn.clone());
        kdt.insert(pn,());
    }

    //dbg!(&kdt);
    let mut success = 0;

    for _ in 0..COUNT {
        let x:f64 = rng.gen_range(-100000.0..100000.0);
        let y:f64 = rng.gen_range(-100000.0..100000.0);

        let p = [x,y];
        let expected = nearest(&p,&positions);
        let actual = kdt.nearest_position(&p);

        if (p.euclidean_distance(expected) - p.euclidean_distance(&actual.unwrap())) < 100. {
            success += 1;
        } else {
            dbg!(expected,actual.unwrap(),p.euclidean_distance(expected),p.euclidean_distance(&actual.unwrap()));
        }
    }

    println!("正答率 {}%",success as f64 / COUNT as f64 * 100.);
}
use egg::*;
use std::io::BufRead;
use std::time::{Duration, Instant};

define_language! {
    enum L {
        Num(i64),
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "-" = Sub([Id; 2]),
        "neg" = Neg([Id; 1]),
        "<<" = Shl([Id; 2]),
        ">>" = Shr([Id; 2]),
        "//" = Div([Id; 2]),
        "%" = Mod([Id; 2]),
        "&" = And([Id; 2]),
        "|" = Or([Id; 2]),
        "^" = Xor([Id; 2]),
        Sym(Symbol),
        Other(Symbol, Vec<Id>),
    }
}

#[derive(Default)]
struct Fold;
impl Analysis<L> for Fold {
    type Data = Option<i64>;
    fn make(eg: &EGraph<L, Self>, e: &L) -> Self::Data {
        let x = |i: &Id| eg[*i].data;
        Some(match e {
            L::Num(n) => *n,
            L::Add([a, b]) => x(a)?.wrapping_add(x(b)?),
            L::Mul([a, b]) => x(a)?.wrapping_mul(x(b)?),
            L::Sub([a, b]) => x(a)?.wrapping_sub(x(b)?),
            L::Neg([a]) => x(a)?.wrapping_neg(),
            L::Shl([a, b]) => x(a)?.wrapping_shl((x(b)? & 63) as u32),
            L::Shr([a, b]) => x(a)?.wrapping_shr((x(b)? & 63) as u32),
            L::And([a, b]) => x(a)? & x(b)?,
            L::Or([a, b]) => x(a)? | x(b)?,
            L::Xor([a, b]) => x(a)? ^ x(b)?,
            _ => return None,
        })
    }
    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        merge_option(a, b, |x, y| {
            assert_eq!(*x, y, "constant folding disagreed");
            DidMerge(false, false)
        })
    }
    fn modify(eg: &mut EGraph<L, Self>, id: Id) {
        if let Some(c) = eg[id].data {
            let n = eg.add(L::Num(c));
            eg.union(id, n);
        }
    }
}

fn rules() -> Vec<Rewrite<L, Fold>> {
    let mut v: Vec<Rewrite<L, Fold>> = vec![
        rewrite!("comm+"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("comm*"; "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("assoc+"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rewrite!("assoc+r"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rewrite!("assoc*"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rewrite!("assoc*r"; "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),
        rewrite!("distrib"; "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
        rewrite!("factor"; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
        rewrite!("add0"; "(+ ?a 0)" => "?a"),
        rewrite!("mul1"; "(* ?a 1)" => "?a"),
        rewrite!("mul0"; "(* ?a 0)" => "0"),
        rewrite!("sub"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
        rewrite!("neg"; "(neg ?a)" => "(* -1 ?a)"),
        // like terms, c1*x + c2*x -> (c1+c2)*x, bare x counting as 1*x
        rewrite!("like"; "(+ ?a ?a)" => "(* 2 ?a)"),
        rewrite!("like-cc"; "(+ (* ?c ?x) (* ?d ?x))" => "(* (+ ?c ?d) ?x)"),
        rewrite!("like-c1"; "(+ (* ?c ?x) ?x)" => "(* (+ ?c 1) ?x)"),
        rewrite!("like-1c"; "(+ ?x (* ?c ?x))" => "(* (+ 1 ?c) ?x)"),
    ];
    for k in 0..64i64 {
        let m = 1i64.wrapping_shl(k as u32);
        v.push(Rewrite::new(
            format!("shl{}", k),
            format!("(<< ?a {})", k).parse::<Pattern<L>>().unwrap(),
            format!("(* ?a {})", m).parse::<Pattern<L>>().unwrap(),
        ).unwrap());
    }
    v
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let nodes: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(10_000);
    let secs: f64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(2.0);
    let rs = rules();
    for line in std::io::stdin().lock().lines() {
        let line = line.unwrap();
        let f: Vec<&str> = line.split('\t').collect();
        if f.len() < 4 { continue; }
        let a: RecExpr<L> = f[2].parse().unwrap();
        let b: RecExpr<L> = f[3].parse().unwrap();
        let t0 = Instant::now();
        let mut runner = Runner::<L, Fold, ()>::default()
            .with_node_limit(nodes)
            .with_time_limit(Duration::from_secs_f64(secs))
            .with_iter_limit(30)
            .with_expr(&a)
            .with_expr(&b)
            .with_hook(|r| {
                if r.egraph.find(r.roots[0]) == r.egraph.find(r.roots[1]) {
                    Err("proved".into())
                } else {
                    Ok(())
                }
            })
            .run(&rs);
        let proved = runner.egraph.find(runner.roots[0]) == runner.egraph.find(runner.roots[1]);
        let stop = format!("{:?}", runner.stop_reason).replace('"', "'");
        println!(
            "{{\"id\":\"{}\",\"suite\":\"{}\",\"status\":\"{}\",\"enodes\":{},\"iters\":{},\"micros\":{},\"stop\":\"{}\"}}",
            f[0], f[1], if proved { "proved" } else { "stuck" }, runner.egraph.total_size(),
            runner.iterations.len(), t0.elapsed().as_micros(), stop.chars().take(60).collect::<String>()
        );
    }
    let hwm = std::fs::read_to_string("/proc/self/status").ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).map(|l| l.to_string()))
        .and_then(|l| l.split_whitespace().nth(1).map(|x| x.to_string()))
        .unwrap_or_else(|| "0".into());
    println!("{{\"summary\":true,\"vmhwm_kb\":{}}}", hwm);
}

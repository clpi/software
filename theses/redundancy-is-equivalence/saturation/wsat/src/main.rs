//! wsat: bounded, witness-driven equality saturation over the one graph.
//!
//! Engines, all on the same e-graph, rules, witness rows and fuel:
//!   saturate  apply every match of every rule each round, to the bound
//!   greedy    plain greedy (shrink term size) with per-rule exponential backoff
//!   witness   composite heuristic, bidirectional cones, split-quota beam,
//!             provenance credit with UCB1, three-axis fuel with dividend
//!   eval      exhaustive evaluation over the resolved witness points
//!
//! Input: obligations, one per line: id \t suite \t src \t wit (s-expressions).
//! Output: one JSON object per obligation per run on stdout.
//! std only.

use std::collections::{BinaryHeap, HashMap, HashSet};
use std::fmt::Write as _;
use std::io::{self, BufRead};
use std::time::Instant;

// ------------------------------------------------------------------ symbols

thread_local! {
    static SYMS: std::cell::RefCell<(Vec<String>, HashMap<String, u32>)> =
        std::cell::RefCell::new((Vec::new(), HashMap::new()));
}

fn sym(s: &str) -> u32 {
    SYMS.with(|t| {
        let mut t = t.borrow_mut();
        if let Some(&i) = t.1.get(s) {
            return i;
        }
        let i = t.0.len() as u32;
        t.0.push(s.to_string());
        t.1.insert(s.to_string(), i);
        i
    })
}

fn symname(i: u32) -> String {
    SYMS.with(|t| t.borrow().0[i as usize].clone())
}

// -------------------------------------------------------------------- terms

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
enum Op {
    Var(u32),
    Const(i64),
    Add,
    Mul,
    Sub,
    Neg,
    Shl,
    Shr,
    Div,
    Mod,
    And,
    Or,
    Xor,
    Idx(u32),
    Call(u32),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct T {
    op: Op,
    kids: Vec<T>,
}

fn leaf(op: Op) -> T {
    T { op, kids: vec![] }
}

fn size(t: &T) -> u64 {
    1 + t.kids.iter().map(size).sum::<u64>()
}

fn show(t: &T, out: &mut String) {
    match t.op {
        Op::Var(s) => out.push_str(&symname(s)),
        Op::Const(c) => {
            let _ = write!(out, "{}", c);
        }
        _ => {
            out.push('(');
            let h = match t.op {
                Op::Add => "+".to_string(),
                Op::Mul => "*".to_string(),
                Op::Sub => "-".to_string(),
                Op::Neg => "neg".to_string(),
                Op::Shl => "<<".to_string(),
                Op::Shr => ">>".to_string(),
                Op::Div => "//".to_string(),
                Op::Mod => "%".to_string(),
                Op::And => "&".to_string(),
                Op::Or => "|".to_string(),
                Op::Xor => "^".to_string(),
                Op::Idx(s) => format!("idx {}", symname(s)),
                Op::Call(s) => format!("call {}", symname(s)),
                _ => unreachable!(),
            };
            out.push_str(&h);
            for k in &t.kids {
                out.push(' ');
                show(k, out);
            }
            out.push(')');
        }
    }
}

fn tokenize(s: &str) -> Vec<String> {
    s.replace('(', " ( ").replace(')', " ) ").split_whitespace().map(|x| x.to_string()).collect()
}

fn parse(tokens: &[String], pos: &mut usize) -> T {
    let tok = &tokens[*pos];
    *pos += 1;
    if tok != "(" {
        if let Ok(v) = tok.parse::<i64>() {
            return leaf(Op::Const(v));
        }
        return leaf(Op::Var(sym(tok)));
    }
    let head = tokens[*pos].clone();
    *pos += 1;
    let mut kids = Vec::new();
    let op = match head.as_str() {
        "+" => Op::Add,
        "*" => Op::Mul,
        "-" => Op::Sub,
        "neg" => Op::Neg,
        "<<" => Op::Shl,
        ">>" => Op::Shr,
        "//" => Op::Div,
        "%" => Op::Mod,
        "&" => Op::And,
        "|" => Op::Or,
        "^" => Op::Xor,
        "idx" => {
            let s = tokens[*pos].clone();
            *pos += 1;
            Op::Idx(sym(&s))
        }
        "call" => {
            let s = tokens[*pos].clone();
            *pos += 1;
            Op::Call(sym(&s))
        }
        other => panic!("unknown head {}", other),
    };
    while tokens[*pos] != ")" {
        kids.push(parse(tokens, pos));
    }
    *pos += 1;
    // n-ary + and * fold to the left
    if (op == Op::Add || op == Op::Mul) && kids.len() > 2 {
        let mut it = kids.into_iter();
        let mut acc = it.next().unwrap();
        for k in it {
            acc = T { op, kids: vec![acc, k] };
        }
        return acc;
    }
    T { op, kids }
}

fn parse_str(s: &str) -> T {
    let toks = tokenize(s);
    let mut p = 0;
    parse(&toks, &mut p)
}

fn mix(mut z: u64) -> u64 {
    z = z.wrapping_add(0x9E3779B97F4A7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
    z ^ (z >> 31)
}

/// Wrapping i64 semantics (Z / 2^64 for + - * and shifts); arrays and
/// calls are fixed pseudo-random functions of their arguments.
// node evaluations, counted for every engine (one shared cost unit);
// the independent audit on fresh points is excluded
static EVALS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn evals_now() -> u64 {
    EVALS.load(std::sync::atomic::Ordering::Relaxed)
}

fn eval(t: &T, env: &HashMap<u32, i64>) -> i64 {
    EVALS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let k = |i: usize| eval(&t.kids[i], env);
    match t.op {
        Op::Var(s) => *env.get(&s).unwrap_or(&((mix(s as u64) as i64) & 0xff)),
        Op::Const(c) => c,
        Op::Add => k(0).wrapping_add(k(1)),
        Op::Mul => k(0).wrapping_mul(k(1)),
        Op::Sub => k(0).wrapping_sub(k(1)),
        Op::Neg => k(0).wrapping_neg(),
        Op::Shl => k(0).wrapping_shl((k(1) & 63) as u32),
        Op::Shr => k(0).wrapping_shr((k(1) & 63) as u32),
        Op::Div => {
            let b = k(1);
            if b == 0 { 0 } else { k(0).wrapping_div_euclid(b) }
        }
        Op::Mod => {
            let b = k(1);
            if b == 0 { 0 } else { k(0).wrapping_rem_euclid(b) }
        }
        Op::And => k(0) & k(1),
        Op::Or => k(0) | k(1),
        Op::Xor => k(0) ^ k(1),
        Op::Idx(s) => (mix((s as u64) << 32 ^ (k(0) as u64)) & 0xffff) as i64,
        Op::Call(s) => {
            let mut h = mix(s as u64 ^ 0xC0FFEE);
            for i in 0..t.kids.len() {
                h = mix(h ^ (k(i) as u64));
            }
            (h & 0xffff) as i64
        }
    }
}

fn vars(t: &T, out: &mut Vec<u32>) {
    if let Op::Var(s) = t.op {
        if !out.contains(&s) {
            out.push(s);
        }
    }
    for k in &t.kids {
        vars(k, out);
    }
}

/// Witness points: deterministic environments over the variables.
/// Small values first (they reach edge cases), then mixed widths.
fn points(vs: &[u32], n: usize, seed: u64) -> Vec<HashMap<u32, i64>> {
    let mut out = Vec::new();
    for i in 0..n {
        let mut env = HashMap::new();
        for (j, &v) in vs.iter().enumerate() {
            let h = mix(seed ^ ((i as u64) << 16) ^ (j as u64) ^ ((v as u64) << 40));
            let val = match i % 4 {
                0 => (h % 7) as i64 - 3,
                1 => (h & 0xff) as i64,
                2 => (h & 0xffff_ffff) as i64,
                _ => h as i64,
            };
            env.insert(v, val);
        }
        out.push(env);
    }
    out
}

// ------------------------------------------------------------------ e-graph

type Id = u32;
type NId = u32;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct ENode {
    op: Op,
    kids: Vec<Id>,
}

struct EGraph {
    uf: Vec<Id>,
    nodes: Vec<ENode>,
    node_class: Vec<Id>,
    memo: HashMap<ENode, NId>,
    class_nodes: Vec<Vec<NId>>,
    class_parents: Vec<Vec<NId>>,
    pending: Vec<Id>,
    best: Vec<(u64, NId)>,
    match_steps: u64,
}

impl EGraph {
    fn new() -> Self {
        EGraph {
            uf: vec![],
            nodes: vec![],
            node_class: vec![],
            memo: HashMap::new(),
            class_nodes: vec![],
            class_parents: vec![],
            pending: vec![],
            best: vec![],
            match_steps: 0,
        }
    }

    fn find(&self, mut a: Id) -> Id {
        while self.uf[a as usize] != a {
            a = self.uf[a as usize];
        }
        a
    }

    fn compress(&mut self, a: Id) -> Id {
        let r = self.find(a);
        let mut x = a;
        while self.uf[x as usize] != r {
            let n = self.uf[x as usize];
            self.uf[x as usize] = r;
            x = n;
        }
        r
    }

    fn canon(&self, n: &ENode) -> ENode {
        ENode { op: n.op, kids: n.kids.iter().map(|&k| self.find(k)).collect() }
    }

    fn lookup_node(&self, n: &ENode) -> Option<NId> {
        let c = self.canon(n);
        self.memo.get(&c).copied()
    }

    /// Add a node; returns (class, node, fresh).
    fn add(&mut self, n: ENode) -> (Id, NId, bool) {
        let c = self.canon(&n);
        if let Some(&nid) = self.memo.get(&c) {
            return (self.find(self.node_class[nid as usize]), nid, false);
        }
        let nid = self.nodes.len() as NId;
        let cid = self.uf.len() as Id;
        self.uf.push(cid);
        self.class_nodes.push(vec![nid]);
        self.class_parents.push(vec![]);
        self.best.push((u64::MAX, nid));
        for &k in &c.kids {
            let r = self.find(k);
            self.class_parents[r as usize].push(nid);
        }
        self.nodes.push(c.clone());
        self.node_class.push(cid);
        self.memo.insert(c, nid);
        (cid, nid, true)
    }

    fn add_term(&mut self, t: &T, fresh: &mut Vec<NId>) -> Id {
        let kids: Vec<Id> = t.kids.iter().map(|k| self.add_term(k, fresh)).collect();
        let (c, nid, f) = self.add(ENode { op: t.op, kids });
        if f {
            fresh.push(nid);
        }
        c
    }

    fn lookup_term(&self, t: &T) -> Option<Id> {
        let mut kids = vec![];
        for k in &t.kids {
            kids.push(self.lookup_term(k)?);
        }
        self.lookup_node(&ENode { op: t.op, kids }).map(|n| self.find(self.node_class[n as usize]))
    }

    fn union(&mut self, a: Id, b: Id) -> bool {
        let (ra, rb) = (self.compress(a), self.compress(b));
        if ra == rb {
            return false;
        }
        let (big, small) = if self.class_nodes[ra as usize].len() >= self.class_nodes[rb as usize].len() {
            (ra, rb)
        } else {
            (rb, ra)
        };
        self.uf[small as usize] = big;
        let ns = std::mem::take(&mut self.class_nodes[small as usize]);
        self.class_nodes[big as usize].extend(ns);
        let ps = std::mem::take(&mut self.class_parents[small as usize]);
        self.class_parents[big as usize].extend(ps);
        self.pending.push(big);
        true
    }

    /// Restore congruence. Calls `cong(p, q)` for each pair of parent
    /// nodes found congruent. Each step costs one match unit.
    fn rebuild(&mut self) -> Vec<(NId, NId)> {
        let mut congs = vec![];
        while let Some(c) = self.pending.pop() {
            let c = self.find(c);
            let parents = self.class_parents[c as usize].clone();
            for p in parents {
                self.match_steps += 1;
                let cn = self.canon(&self.nodes[p as usize]);
                if let Some(&q) = self.memo.get(&cn) {
                    if q != p {
                        let (cp, cq) = (self.find(self.node_class[p as usize]), self.find(self.node_class[q as usize]));
                        if cp != cq {
                            self.union(cp, cq);
                            congs.push((p, q));
                        }
                    }
                } else {
                    self.memo.insert(cn.clone(), p);
                }
                self.nodes[p as usize] = cn;
            }
        }
        congs
    }

    fn classes(&self) -> Vec<Id> {
        (0..self.uf.len() as Id).filter(|&c| self.uf[c as usize] == c).collect()
    }

    /// Size-based extraction to a fixpoint (always acyclic: a node's
    /// cost exceeds each child's).
    fn extract(&mut self) {
        for b in self.best.iter_mut() {
            b.0 = u64::MAX;
        }
        let mut changed = true;
        let mut iters = 0;
        while changed && iters < 200 {
            changed = false;
            iters += 1;
            for nid in 0..self.nodes.len() {
                let n = &self.nodes[nid];
                let mut cost: u64 = 1;
                let mut ok = true;
                for &k in &n.kids {
                    let r = self.find(k);
                    let kc = self.best[r as usize].0;
                    if kc == u64::MAX {
                        ok = false;
                        break;
                    }
                    cost = cost.saturating_add(kc);
                }
                if !ok {
                    continue;
                }
                let r = self.find(self.node_class[nid]) as usize;
                if cost < self.best[r].0 {
                    self.best[r] = (cost, nid as NId);
                    changed = true;
                }
            }
        }
    }

    fn rep(&self, c: Id) -> T {
        let r = self.find(c);
        let (_, nid) = self.best[r as usize];
        let n = &self.nodes[nid as usize];
        T { op: n.op, kids: n.kids.iter().map(|&k| self.rep(k)).collect() }
    }

    /// Classes reachable from `c` (its cone), at most `cap`.
    fn cone(&self, c: Id, cap: usize) -> Vec<Id> {
        let mut seen = HashSet::new();
        let mut stack = vec![self.find(c)];
        let mut out = vec![];
        while let Some(x) = stack.pop() {
            if !seen.insert(x) || out.len() >= cap {
                continue;
            }
            out.push(x);
            for &n in &self.class_nodes[x as usize] {
                for &k in &self.nodes[n as usize].kids {
                    stack.push(self.find(k));
                }
            }
        }
        out
    }
}

// --------------------------------------------------------------- provenance

const RULE_CONG: u16 = 1000;
const RULE_WITNESS: u16 = 1001;
const F_BRIDGE: u32 = 1;
const F_MULTI: u32 = 4;

/// 16 bytes: four fit in a 64-byte line.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
struct ProvNode {
    rule: u16,
    depth: u16,
    primary: u32,
    secondary: u32,
    flags: u32,
}

const BASE: u32 = 0;

/// Per-epoch derivation arena. Index 0 is BASE (pre-existing e-nodes).
struct EpochProv {
    nodes: Vec<ProvNode>,
    overflow: Vec<u32>,
    enode_to_prov: Vec<u32>,
    naive: bool,               // ablation: keep every re-derivation as an extra edge
    naive_extra: Vec<(u32, u32)>,
    first_node: usize,         // e-nodes below this index existed before the epoch
}

impl EpochProv {
    fn new(cap: usize, naive: bool) -> Self {
        let mut nodes = Vec::with_capacity(cap + 1);
        nodes.push(ProvNode { rule: RULE_WITNESS, depth: 0, primary: BASE, secondary: BASE, flags: 0 });
        EpochProv { nodes, overflow: vec![], enode_to_prov: vec![], naive, naive_extra: vec![], first_node: 0 }
    }

    fn start(&mut self, enodes: usize) {
        self.nodes.truncate(1);
        self.overflow.clear();
        self.enode_to_prov.clear();
        self.naive_extra.clear();
        self.first_node = enodes;
    }

    fn get(&self, n: NId) -> u32 {
        *self.enode_to_prov.get(n as usize).unwrap_or(&BASE)
    }

    fn depth(&self, p: u32) -> u16 {
        self.nodes[p as usize].depth
    }

    /// Record a derivation of e-node `n` from premises. First parent
    /// wins unless the new derivation is strictly shallower.
    fn record(&mut self, n: NId, rule: u16, premises: &[u32], bridge: bool) -> u32 {
        let depth = 1 + premises.iter().map(|&p| self.depth(p)).max().unwrap_or(0);
        let (primary, secondary, mut flags) = match premises.len() {
            0 => (BASE, BASE, 0),
            1 => (premises[0], BASE, 0),
            2 => (premises[0], premises[1], 0),
            _ => {
                let off = self.overflow.len() as u32;
                self.overflow.push((premises.len() - 1) as u32);
                self.overflow.extend_from_slice(&premises[1..]);
                (premises[0], off, F_MULTI)
            }
        };
        if bridge {
            flags |= F_BRIDGE;
        }
        if self.enode_to_prov.len() <= n as usize {
            self.enode_to_prov.resize(n as usize + 1, BASE);
        }
        let cur = self.enode_to_prov[n as usize];
        let node = ProvNode { rule, depth, primary, secondary, flags };
        if cur == BASE {
            let id = self.nodes.len() as u32;
            self.nodes.push(node);
            self.enode_to_prov[n as usize] = id;
            id
        } else {
            if self.naive {
                // every re-derivation kept: cycles and double paths appear
                for &p in premises {
                    self.naive_extra.push((cur, p));
                }
            } else if depth < self.nodes[cur as usize].depth {
                self.nodes[cur as usize] = node;
            }
            cur
        }
    }

    fn premises(&self, p: u32) -> Vec<u32> {
        let n = self.nodes[p as usize];
        let mut out = vec![];
        if n.primary != BASE {
            out.push(n.primary);
        }
        if n.flags & F_MULTI != 0 {
            let off = n.secondary as usize;
            let len = self.overflow[off] as usize;
            out.extend_from_slice(&self.overflow[off + 1..off + 1 + len]);
        } else if n.secondary != BASE {
            out.push(n.secondary);
        }
        if self.naive {
            for &(a, b) in &self.naive_extra {
                if a == p {
                    out.push(b);
                }
            }
        }
        out
    }

    /// True when the arena's premise edges form a DAG.
    fn acyclic(&self) -> bool {
        let n = self.nodes.len();
        let mut state = vec![0u8; n];
        for s in 1..n {
            if state[s] != 0 {
                continue;
            }
            let mut stack = vec![(s as u32, false)];
            while let Some((x, done)) = stack.pop() {
                if done {
                    state[x as usize] = 2;
                    continue;
                }
                if state[x as usize] == 2 {
                    continue;
                }
                if state[x as usize] == 1 {
                    continue;
                }
                state[x as usize] = 1;
                stack.push((x, true));
                for p in self.premises(x) {
                    if state[p as usize] == 1 {
                        return false;
                    }
                    if state[p as usize] == 0 {
                        stack.push((p, false));
                    }
                }
            }
        }
        true
    }

    fn bytes(&self) -> usize {
        self.nodes.len() * std::mem::size_of::<ProvNode>() + self.overflow.len() * 4 + self.enode_to_prov.len() * 4
    }
}

// -------------------------------------------------------------------- rules

const NRULES: usize = 19;
const RULE_NAMES: [&str; NRULES] = [
    "comm+", "comm*", "assoc+", "assoc+r", "assoc*", "assoc*r", "distrib", "factor", "fold",
    "add0", "mul1", "mul0", "sub", "neg", "shl", "like", "acnorm", "gen", "linnorm",
];
const R_LIN: usize = 18;
const R_ACNORM: usize = 16;
const R_GEN: usize = 17;

/// A right-hand side to build: a tree over existing classes.
#[derive(Clone, Debug)]
enum Pat {
    C(Id),
    N(Op, Vec<Pat>),
}

struct Match {
    rule: usize,
    node: NId,
    class: Id,
    rhs: Pat,
    premises: Vec<NId>,
}

fn konst(eg: &EGraph, c: Id) -> Option<i64> {
    let r = eg.find(c);
    for &n in &eg.class_nodes[r as usize] {
        if let Op::Const(v) = eg.nodes[n as usize].op {
            return Some(v);
        }
    }
    None
}

fn nodes_of(eg: &EGraph, c: Id, op: Op) -> Vec<NId> {
    let r = eg.find(c);
    eg.class_nodes[r as usize].iter().copied().filter(|&n| eg.nodes[n as usize].op == op).collect()
}

/// Flatten an AC tree along extracted representatives.
fn flatten(eg: &EGraph, c: Id, op: Op, out: &mut Vec<Id>, depth: usize) {
    let r = eg.find(c);
    let (_, nid) = eg.best[r as usize];
    let n = &eg.nodes[nid as usize];
    if n.op == op && depth < 64 {
        flatten(eg, n.kids[0], op, out, depth + 1);
        flatten(eg, n.kids[1], op, out, depth + 1);
    } else {
        out.push(r);
    }
}

fn coef(eg: &EGraph, c: Id) -> Vec<(i64, Id, Option<NId>)> {
    // (coefficient, base class, node) readings of a class as c*x or x
    let r = eg.find(c);
    let mut out = vec![(1, r, None)];
    for &n in &eg.class_nodes[r as usize] {
        let nd = &eg.nodes[n as usize];
        if nd.op == Op::Mul {
            if let Some(k) = konst(eg, nd.kids[0]) {
                out.push((k, eg.find(nd.kids[1]), Some(n)));
            }
        }
    }
    out
}

fn matches_at(eg: &mut EGraph, nid: NId, rules: &[bool], out: &mut Vec<Match>, quota: &mut i64) {
    let n = eg.nodes[nid as usize].clone();
    let class = eg.find(eg.node_class[nid as usize]);
    let k = |i: usize| n.kids[i];
    let push = |eg: &mut EGraph, out: &mut Vec<Match>, quota: &mut i64, rule: usize, rhs: Pat, prem: Vec<NId>| {
        eg.match_steps += 1;
        *quota -= 1;
        out.push(Match { rule, node: nid, class, rhs, premises: prem });
    };
    let on = |r: usize| rules[r];
    match n.op {
        Op::Add => {
            if on(0) {
                push(eg, out, quota, 0, Pat::N(Op::Add, vec![Pat::C(k(1)), Pat::C(k(0))]), vec![nid]);
            }
            if on(2) {
                for m in nodes_of(eg, k(0), Op::Add) {
                    if *quota <= 0 { return; }
                    let mk = eg.nodes[m as usize].kids.clone();
                    push(eg, out, quota, 2, Pat::N(Op::Add, vec![Pat::C(mk[0]), Pat::N(Op::Add, vec![Pat::C(mk[1]), Pat::C(k(1))])]), vec![nid, m]);
                }
            }
            if on(3) {
                for m in nodes_of(eg, k(1), Op::Add) {
                    if *quota <= 0 { return; }
                    let mk = eg.nodes[m as usize].kids.clone();
                    push(eg, out, quota, 3, Pat::N(Op::Add, vec![Pat::N(Op::Add, vec![Pat::C(k(0)), Pat::C(mk[0])]), Pat::C(mk[1])]), vec![nid, m]);
                }
            }
            if on(7) {
                // factor: a*b + a*c -> a*(b+c), joining over the two classes
                let xs = nodes_of(eg, k(0), Op::Mul);
                let ys = nodes_of(eg, k(1), Op::Mul);
                for &x in &xs {
                    for &y in &ys {
                        if *quota <= 0 { return; }
                        eg.match_steps += 1;
                        *quota -= 1;
                        let (xk, yk) = (eg.nodes[x as usize].kids.clone(), eg.nodes[y as usize].kids.clone());
                        if eg.find(xk[0]) == eg.find(yk[0]) {
                            push(eg, out, quota, 7, Pat::N(Op::Mul, vec![Pat::C(xk[0]), Pat::N(Op::Add, vec![Pat::C(xk[1]), Pat::C(yk[1])])]), vec![nid, x, y]);
                        }
                    }
                }
            }
            if on(8) {
                if let (Some(a), Some(b)) = (konst(eg, k(0)), konst(eg, k(1))) {
                    push(eg, out, quota, 8, Pat::N(Op::Const(a.wrapping_add(b)), vec![]), vec![nid]);
                }
            }
            if on(9) {
                if konst(eg, k(1)) == Some(0) {
                    push(eg, out, quota, 9, Pat::C(k(0)), vec![nid]);
                }
                if konst(eg, k(0)) == Some(0) {
                    push(eg, out, quota, 9, Pat::C(k(1)), vec![nid]);
                }
            }
            if on(15) {
                // like terms: c1*x + c2*x -> (c1+c2)*x
                let (ca, cb) = (coef(eg, k(0)), coef(eg, k(1)));
                for &(c1, x1, n1) in &ca {
                    for &(c2, x2, n2) in &cb {
                        if *quota <= 0 { return; }
                        if x1 == x2 {
                            let mut prem = vec![nid];
                            prem.extend(n1);
                            prem.extend(n2);
                            push(eg, out, quota, 15, Pat::N(Op::Mul, vec![Pat::N(Op::Const(c1.wrapping_add(c2)), vec![]), Pat::C(x1)]), prem);
                        }
                    }
                }
            }
            if on(R_ACNORM) {
                acnorm(eg, out, quota, nid, class, Op::Add);
            }
        }
        Op::Mul => {
            if on(1) {
                push(eg, out, quota, 1, Pat::N(Op::Mul, vec![Pat::C(k(1)), Pat::C(k(0))]), vec![nid]);
            }
            if on(4) {
                for m in nodes_of(eg, k(0), Op::Mul) {
                    if *quota <= 0 { return; }
                    let mk = eg.nodes[m as usize].kids.clone();
                    push(eg, out, quota, 4, Pat::N(Op::Mul, vec![Pat::C(mk[0]), Pat::N(Op::Mul, vec![Pat::C(mk[1]), Pat::C(k(1))])]), vec![nid, m]);
                }
            }
            if on(5) {
                for m in nodes_of(eg, k(1), Op::Mul) {
                    if *quota <= 0 { return; }
                    let mk = eg.nodes[m as usize].kids.clone();
                    push(eg, out, quota, 5, Pat::N(Op::Mul, vec![Pat::N(Op::Mul, vec![Pat::C(k(0)), Pat::C(mk[0])]), Pat::C(mk[1])]), vec![nid, m]);
                }
            }
            if on(6) {
                for m in nodes_of(eg, k(1), Op::Add) {
                    if *quota <= 0 { return; }
                    let mk = eg.nodes[m as usize].kids.clone();
                    push(eg, out, quota, 6, Pat::N(Op::Add, vec![Pat::N(Op::Mul, vec![Pat::C(k(0)), Pat::C(mk[0])]), Pat::N(Op::Mul, vec![Pat::C(k(0)), Pat::C(mk[1])])]), vec![nid, m]);
                }
            }
            if on(8) {
                if let (Some(a), Some(b)) = (konst(eg, k(0)), konst(eg, k(1))) {
                    push(eg, out, quota, 8, Pat::N(Op::Const(a.wrapping_mul(b)), vec![]), vec![nid]);
                }
            }
            if on(10) {
                if konst(eg, k(1)) == Some(1) {
                    push(eg, out, quota, 10, Pat::C(k(0)), vec![nid]);
                }
                if konst(eg, k(0)) == Some(1) {
                    push(eg, out, quota, 10, Pat::C(k(1)), vec![nid]);
                }
            }
            if on(11) && (konst(eg, k(0)) == Some(0) || konst(eg, k(1)) == Some(0)) {
                push(eg, out, quota, 11, Pat::N(Op::Const(0), vec![]), vec![nid]);
            }
            if on(R_ACNORM) {
                acnorm(eg, out, quota, nid, class, Op::Mul);
            }
        }
        Op::Sub => {
            if on(12) {
                push(eg, out, quota, 12, Pat::N(Op::Add, vec![Pat::C(k(0)), Pat::N(Op::Mul, vec![Pat::N(Op::Const(-1), vec![]), Pat::C(k(1))])]), vec![nid]);
            }
            if on(8) {
                if let (Some(a), Some(b)) = (konst(eg, k(0)), konst(eg, k(1))) {
                    push(eg, out, quota, 8, Pat::N(Op::Const(a.wrapping_sub(b)), vec![]), vec![nid]);
                }
            }
        }
        Op::Neg => {
            if on(13) {
                push(eg, out, quota, 13, Pat::N(Op::Mul, vec![Pat::N(Op::Const(-1), vec![]), Pat::C(k(0))]), vec![nid]);
            }
        }
        Op::Shl => {
            if on(14) {
                if let Some(s) = konst(eg, k(1)) {
                    if (0..63).contains(&s) {
                        push(eg, out, quota, 14, Pat::N(Op::Mul, vec![Pat::C(k(0)), Pat::N(Op::Const(1i64 << s), vec![])]), vec![nid]);
                    }
                }
            }
        }
        _ => {}
    }
    if on(R_LIN) && *quota > 0 && matches!(n.op, Op::Add | Op::Sub | Op::Mul | Op::Neg | Op::Shl) {
        let rc = eg.rep(class);
        let nf = normal(&rc);
        if nf != rc {
            push(eg, out, quota, R_LIN, t_to_pat(&nf), vec![nid]);
        }
    }
    if on(R_GEN) && *quota > 0 {
        // generative: a -> (a + 1) - 1 (sound, allocates a fresh chain)
        push(eg, out, quota, R_GEN, Pat::N(Op::Sub, vec![Pat::N(Op::Add, vec![Pat::C(class), Pat::N(Op::Const(1), vec![])]), Pat::N(Op::Const(1), vec![])]), vec![nid]);
    }
}

fn ckey(eg: &EGraph, c: Id) -> String {
    let mut s = String::new();
    show(&eg.rep(c), &mut s);
    s
}

fn acnorm(eg: &mut EGraph, out: &mut Vec<Match>, quota: &mut i64, nid: NId, class: Id, op: Op) {
    let mut ops = vec![];
    flatten(eg, class, op, &mut ops, 0);
    if ops.len() < 3 {
        return;
    }
    let mut keyed: Vec<(String, Id)> = ops.iter().map(|&c| (ckey(eg, c), c)).collect();
    keyed.sort();
    let mut it = keyed.into_iter();
    let mut acc = Pat::C(it.next().unwrap().1);
    for (_, c) in it {
        acc = Pat::N(op, vec![acc, Pat::C(c)]);
    }
    eg.match_steps += 1;
    *quota -= 1;
    out.push(Match { rule: R_ACNORM, node: nid, class, rhs: acc, premises: vec![nid] });
}

fn materialize(eg: &EGraph, p: &Pat) -> T {
    match p {
        Pat::C(c) => eg.rep(*c),
        Pat::N(op, kids) => T { op: *op, kids: kids.iter().map(|k| materialize(eg, k)).collect() },
    }
}

fn build(eg: &mut EGraph, p: &Pat, fresh: &mut Vec<NId>, max_new: i64) -> Option<(Id, NId)> {
    match p {
        Pat::C(c) => {
            let r = eg.find(*c);
            Some((r, eg.best[r as usize].1))
        }
        Pat::N(op, kids) => {
            let mut ks = vec![];
            for k in kids {
                ks.push(build(eg, k, fresh, max_new)?.0);
            }
            let node = ENode { op: *op, kids: ks };
            if eg.lookup_node(&node).is_none() && fresh.len() as i64 >= max_new {
                return None;
            }
            let (c, nid, f) = eg.add(node);
            if f {
                fresh.push(nid);
            }
            Some((c, nid))
        }
    }
}

// ------------------------------------------------------------- linear forms

/// A term read as a linear form: coefficients over normalized atoms plus
/// a constant. Non-linear subterms are atoms whose arguments are
/// normalized recursively.
fn lin(t: &T) -> (Vec<(String, i64, T)>, i64) {
    let mut m: HashMap<String, (i64, T)> = HashMap::new();
    let mut k: i64 = 0;
    lin_into(t, 1, &mut m, &mut k);
    let mut v: Vec<(String, i64, T)> = m.into_iter().filter(|(_, (c, _))| *c != 0).map(|(s, (c, a))| (s, c, a)).collect();
    v.sort_by(|a, b| a.0.cmp(&b.0));
    (v, k)
}

fn lin_into(t: &T, scale: i64, m: &mut HashMap<String, (i64, T)>, k: &mut i64) {
    match t.op {
        Op::Const(c) => *k = k.wrapping_add(scale.wrapping_mul(c)),
        Op::Add => { lin_into(&t.kids[0], scale, m, k); lin_into(&t.kids[1], scale, m, k); }
        Op::Sub => { lin_into(&t.kids[0], scale, m, k); lin_into(&t.kids[1], scale.wrapping_neg(), m, k); }
        Op::Neg => lin_into(&t.kids[0], scale.wrapping_neg(), m, k),
        Op::Mul if matches!(t.kids[0].op, Op::Const(_)) => {
            if let Op::Const(c) = t.kids[0].op { lin_into(&t.kids[1], scale.wrapping_mul(c), m, k) }
        }
        Op::Mul if matches!(t.kids[1].op, Op::Const(_)) => {
            if let Op::Const(c) = t.kids[1].op { lin_into(&t.kids[0], scale.wrapping_mul(c), m, k) }
        }
        Op::Shl if matches!(t.kids[1].op, Op::Const(s) if (0..63).contains(&s)) => {
            if let Op::Const(s) = t.kids[1].op { lin_into(&t.kids[0], scale.wrapping_mul(1i64 << s), m, k) }
        }
        _ => {
            let a = T { op: t.op, kids: t.kids.iter().map(normal).collect() };
            let mut key = String::new();
            show(&a, &mut key);
            let e = m.entry(key).or_insert((0, a));
            e.0 = e.0.wrapping_add(scale);
        }
    }
}

/// The normal form of a linear form: sorted c*atom terms, then the constant.
fn normal(t: &T) -> T {
    let (v, k) = lin(t);
    let mut acc: Option<T> = None;
    for (_, c, a) in v {
        let term = if c == 1 { a } else { T { op: Op::Mul, kids: vec![leaf(Op::Const(c)), a] } };
        acc = Some(match acc { None => term, Some(x) => T { op: Op::Add, kids: vec![x, term] } });
    }
    match acc {
        None => leaf(Op::Const(k)),
        Some(x) if k == 0 => x,
        Some(x) => T { op: Op::Add, kids: vec![x, leaf(Op::Const(k))] },
    }
}

/// Linear-form distance: L1 over coefficients and constant. Zero means
/// the two terms are equal by the ring laws on linear forms.
fn d_lin(a: &T, b: &T) -> i64 {
    let (va, ka) = lin(a);
    let (vb, kb) = lin(b);
    let mut ma: HashMap<String, i64> = va.into_iter().map(|(s, c, _)| (s, c)).collect();
    let mut d: i64 = 0;
    for (s, c, _) in vb {
        let x = ma.remove(&s).unwrap_or(0);
        d = d.saturating_add((x.wrapping_sub(c)).unsigned_abs().min(1 << 40) as i64);
    }
    for (_, x) in ma {
        d = d.saturating_add(x.unsigned_abs().min(1 << 40) as i64);
    }
    if ka != kb { d = d.saturating_add(1); }
    d
}

fn t_to_pat(t: &T) -> Pat {
    Pat::N(t.op, t.kids.iter().map(t_to_pat).collect())
}

// --------------------------------------------------------------- heuristics

fn hist(t: &T, h: &mut HashMap<Op, i64>) {
    *h.entry(t.op).or_insert(0) += 1;
    for k in &t.kids {
        hist(k, h);
    }
}

fn d_bag(a: &T, b: &T) -> i64 {
    let (mut ha, mut hb) = (HashMap::new(), HashMap::new());
    hist(a, &mut ha);
    hist(b, &mut hb);
    let mut d = 0;
    for (k, v) in &ha {
        d += (v - hb.get(k).unwrap_or(&0)).abs();
    }
    for (k, v) in &hb {
        if !ha.contains_key(k) {
            d += v.abs();
        }
    }
    d
}

/// Anti-unify a class against a target term, aligning on any node of the
/// class whose operator matches the target's (not just the representative).
/// Returns the residual pairs (class, target subterm). Bounded by the
/// target's depth, so it terminates on cyclic classes.
fn au_class(eg: &EGraph, c: Id, t: &T, out: &mut Vec<(Id, T)>) {
    au_guided(eg, c, t, out, &[]);
}

/// With witness points, descend into an alignment only when every
/// aligned child pair agrees on them: a child pair the points refute
/// cannot close locally, so the residual stays at the nearest pair that
/// can.
fn au_guided(eg: &EGraph, c: Id, t: &T, out: &mut Vec<(Id, T)>, pts: &[HashMap<u32, i64>]) {
    let r = eg.find(c);
    for &n in &eg.class_nodes[r as usize] {
        let nd = &eg.nodes[n as usize];
        if nd.op == t.op && nd.kids.len() == t.kids.len() {
            let kids = nd.kids.clone();
            if !pts.is_empty() {
                let bad = kids.iter().enumerate().any(|(i, k)| {
                    let rk = eg.rep(*k);
                    pts.iter().take(8).any(|p| eval(&rk, p) != eval(&t.kids[i], p))
                });
                if bad {
                    continue;
                }
            }
            for (i, k) in kids.iter().enumerate() {
                au_guided(eg, *k, &t.kids[i], out, pts);
            }
            return;
        }
    }
    // also accept: class already holds the target term
    if eg.lookup_term(t).map(|x| eg.find(x)) == Some(r) {
        return;
    }
    out.push((r, t.clone()));
}

fn residual(eg: &EGraph, pairs: &[(Id, T)]) -> i64 {
    pairs.iter().map(|(c, t)| (size(&eg.rep(*c)) + size(t)) as i64).sum()
}

// -------------------------------------------------------------------- config

#[derive(Clone)]
struct Cfg {
    engine: String,
    beh: bool,
    au: bool,
    bag: bool,
    lin: bool,
    ent: bool,
    bidir: bool,
    bridge: bool,
    credit: bool,
    dividend: bool,
    depthfuel: bool,
    prov: bool,
    prov_naive: bool,
    use_credit_for_sched: bool,
    alloc: i64,
    matchf: i64,
    depth: u16,
    cap: i64,
    beam: usize,
    quota: i64,
    rules: Vec<bool>,
    npoints: usize,
    rounds: usize,
    label: String,
}

fn base_rules(gen: bool) -> Vec<bool> {
    let mut r = vec![true; NRULES];
    r[R_GEN] = gen;
    r
}

// ---------------------------------------------------------------- UCB table

#[derive(Clone)]
struct RuleStats {
    n: Vec<f64>,
    credit: Vec<f64>,
    total: f64,
    ban_until: Vec<usize>,
    ban_k: Vec<u32>,
}

impl RuleStats {
    fn new() -> Self {
        RuleStats { n: vec![0.0; NRULES], credit: vec![0.0; NRULES], total: 0.0, ban_until: vec![0; NRULES], ban_k: vec![0; NRULES] }
    }
    fn ucb(&self, r: usize) -> f64 {
        if self.n[r] == 0.0 {
            return f64::INFINITY;
        }
        self.credit[r] / self.n[r] + (2.0 * (self.total.max(1.0)).ln() / self.n[r]).sqrt()
    }
}

// --------------------------------------------------------------------- run

struct Outcome {
    status: &'static str, // proved, refuted, exhausted, stuck, fixpoint
    rounds: usize,
    alloc_used: i64,
    match_used: i64,
    refunded: i64,
    enodes: usize,
    classes: usize,
    prov_nodes: usize,
    prov_bytes: usize,
    prov_acyclic: bool,
    walk_steps: u64,
    double_credit: u64,
    cong_credit_to_bridge: f64,
    micros: u128,
    verified: bool,
    rules_used: Vec<usize>,
    evals: u64,
}

struct Ctx<'a> {
    cfg: &'a Cfg,
    stats: &'a mut RuleStats,
}

fn credit_walk(prov: &EpochProv, starts: &[u32], reward: f64, delta: &mut Vec<f64>, walk_steps: &mut u64,
               double: &mut u64, dedupe: bool, cong_to_bridge: &mut f64) {
    // deepest first; each premise credited at most once per merge
    let mut heap: BinaryHeap<(u16, u32, u64)> = BinaryHeap::new();
    let mut acc: HashMap<u32, f64> = HashMap::new();
    let mut visited: HashSet<u32> = HashSet::new();
    let mut via_cong: HashSet<u32> = HashSet::new();
    for &s in starts {
        if s == BASE { continue; }
        *acc.entry(s).or_insert(0.0) += reward / starts.len().max(1) as f64;
        heap.push((prov.depth(s), s, 0));
    }
    let gamma = 0.85;
    while let Some((_, id, _)) = heap.pop() {
        *walk_steps += 1;
        if *walk_steps > 1_000_000 {
            break;
        }
        if id == BASE { continue; }
        if dedupe {
            if !visited.insert(id) { continue; }
        } else if visited.contains(&id) {
            *double += 1;
        } else {
            visited.insert(id);
        }
        let credit = if dedupe { acc.remove(&id).unwrap_or(0.0) } else { *acc.get(&id).unwrap_or(&0.0) };
        if credit < 1e-6 { continue; }
        let n = prov.nodes[id as usize];
        let mult = if n.flags & F_BRIDGE != 0 { 1.5 } else { 1.0 };
        if (n.rule as usize) < NRULES {
            delta[n.rule as usize] += credit * mult;
            if via_cong.contains(&id) && n.flags & F_BRIDGE != 0 {
                *cong_to_bridge += credit * mult;
            }
        }
        let prem = prov.premises(id);
        if prem.is_empty() { continue; }
        let share = gamma * credit / prem.len() as f64;
        for p in prem {
            if p == BASE { continue; }
            if n.rule == RULE_CONG || via_cong.contains(&id) {
                via_cong.insert(p);
            }
            *acc.entry(p).or_insert(0.0) += share;
            heap.push((prov.depth(p), p, 0));
        }
    }
}

fn run_witness(src: &T, wit: &T, ctx: &mut Ctx, pts: &[HashMap<u32, i64>]) -> Outcome {
    let cfg = ctx.cfg;
    let t0 = Instant::now();
    let mut eg = EGraph::new();
    let mut prov = EpochProv::new(cfg.alloc.max(0) as usize + 1, cfg.prov_naive);
    let mut fresh = vec![];
    let cs = eg.add_term(src, &mut fresh);
    let cw = eg.add_term(wit, &mut fresh);
    // the two anchors were given by the witness row: they are BASE
    prov.start(eg.nodes.len());
    let mut depthv: Vec<u16> = vec![0; eg.nodes.len()];
    let mut out = Outcome {
        status: "stuck", rounds: 0, alloc_used: 0, match_used: 0, refunded: 0, enodes: 0, classes: 0,
        prov_nodes: 0, prov_bytes: 0, prov_acyclic: true, walk_steps: 0, double_credit: 0,
        cong_credit_to_bridge: 0.0, micros: 0, verified: true, rules_used: vec![], evals: 0,
    };
    // hard behavioral falsification against the witness row
    if cfg.beh {
        for p in pts {
            if eval(src, p) != eval(wit, p) {
                out.status = "refuted";
                out.micros = t0.elapsed().as_micros();
                return out;
            }
        }
    }
    let mut alloc = cfg.alloc;
    let mut matchf = cfg.matchf;
    let mut cap = cfg.cap;
    let mut delta = vec![0.0; NRULES];
    let mut visits: HashMap<(usize, Op), u32> = HashMap::new();
    let mut used: HashSet<usize> = HashSet::new();
    let mut last_merge_prov: HashMap<Id, u32> = HashMap::new();
    eg.extract();
    let hroot = |eg: &EGraph, bidir: bool| -> i64 {
        let (rs, rw) = (eg.rep(cs), eg.rep(cw));
        let mut a = vec![];
        au_class(eg, cs, &rw, &mut a);
        let mut h = residual(eg, &a);
        if bidir {
            let mut b = vec![];
            au_class(eg, cw, &rs, &mut b);
            h = h.min(residual(eg, &b));
        }
        h
    };
    let mut h_before = hroot(&eg, cfg.bidir);
    for round in 0..cfg.rounds {
        out.rounds = round + 1;
        if eg.find(cs) == eg.find(cw) {
            out.status = "proved";
            break;
        }
        if alloc <= 0 || matchf <= 0 {
            out.status = "exhausted";
            break;
        }
        let (rs, rw) = (eg.rep(cs), eg.rep(cw));
        // targets: (class, target term, side) from anti-unification
        let mut targets: Vec<(Id, T, u8)> = vec![];
        let mut sides: Vec<(Id, T, u8)> = vec![(cs, rw.clone(), 0)];
        if cfg.bidir || cfg.engine == "saturate" {
            sides.push((cw, rs.clone(), 1));
        }
        for (root, tgt, side) in &sides {
            if cfg.au {
                let mut pairs = vec![];
                let guide: &[HashMap<u32, i64>] = if cfg.beh { pts } else { &[] };
                au_guided(&eg, *root, tgt, &mut pairs, guide);
                for (c, t) in pairs {
                    targets.push((c, t, *side));
                }
            } else {
                targets.push((*root, tgt.clone(), *side));
            }
        }
        targets.sort_by_key(|x| (x.0, x.2));
        targets.dedup_by_key(|x| (x.0, x.2));
        // focus classes
        let mut focus: Vec<(Id, T, u8)> = vec![];
        let mut seenf = HashSet::new();
        if cfg.engine == "saturate" {
            // equality saturation: every rule on every class of the graph
            for x in eg.classes() {
                focus.push((x, rw.clone(), 0));
                seenf.insert((x, 0u8));
            }
        }
        for (c, t, side) in &targets {
            let cone = if cfg.au { eg.cone(*c, 12) } else { eg.cone(*c, 100000) };
            for x in cone {
                if seenf.insert((x, *side)) {
                    focus.push((x, t.clone(), *side));
                }
            }
        }
        // rule order by UCB (or fixed order with backoff for greedy)
        let mut order: Vec<usize> = (0..NRULES).filter(|&r| cfg.rules[r]).collect();
        if cfg.engine == "witness" && cfg.credit && cfg.use_credit_for_sched {
            order.sort_by(|&a, &b| ctx.stats.ucb(b).partial_cmp(&ctx.stats.ucb(a)).unwrap());
        }
        let mut rules_now = vec![false; NRULES];
        for &r in &order {
            if cfg.engine == "greedy" || !cfg.credit {
                if ctx.stats.ban_until[r] > round {
                    continue;
                }
            }
            rules_now[r] = true;
        }

        // enumerate matches within the per-round quota
        let mut quota = if cfg.engine == "saturate" { matchf } else { cfg.quota.min(matchf) };
        let before_steps = eg.match_steps;
        let mut cands: Vec<(Match, i64, u8, T)> = vec![];
        'outer: for (c, t, side) in &focus {
            let nodes = eg.class_nodes[eg.find(*c) as usize].clone();
            for nid in nodes {
                if quota <= 0 {
                    break 'outer;
                }
                // AC recognition: acnorm only where the multiset distance is 0
                let mut rn = rules_now.clone();
                if cfg.engine == "witness" && (rn[R_ACNORM] || rn[R_LIN]) {
                    let rc = eg.rep(*c);
                    if rn[R_ACNORM] {
                        rn[R_ACNORM] = cfg.bag && d_bag(&rc, t) == 0 && rc != *t;
                    }
                    if rn[R_LIN] {
                        rn[R_LIN] = cfg.lin && d_lin(&rc, t) == 0 && rc != *t;
                    }
                }
                let mut ms = vec![];
                matches_at(&mut eg, nid, &rn, &mut ms, &mut quota);
                for m in ms {
                    cands.push((m, 0, *side, t.clone()));
                }
            }
        }
        let spent_match = (eg.match_steps - before_steps) as i64;
        matchf -= spent_match;
        out.match_used += spent_match;
        if cands.is_empty() {
            out.status = "stuck";
            break;
        }
        // score
        for cand in cands.iter_mut() {
            let tn = materialize(&eg, &cand.0.rhs);
            let s = match cfg.engine.as_str() {
                "greedy" => size(&tn) as i64 - size(&eg.rep(cand.0.class)) as i64,
                _ => {
                    let mut h = 0;
                    if cfg.au {
                        let mut pairs = vec![];
                        // distance from the would-be term to its target
                        let tmpc = cand.0.class;
                        au_class(&eg, tmpc, &cand.3, &mut pairs);
                        let base = residual(&eg, &pairs);
                        let aun = au_terms(&tn, &cand.3);
                        h += aun.min(base + 1);
                    } else {
                        h += size(&tn) as i64;
                    }
                    if cfg.bag {
                        h += d_bag(&tn, &cand.3);
                    }
                    if cfg.ent {
                        h = h * 64 - (eg.class_nodes[eg.find(cand.0.class) as usize].len() as i64).min(63);
                    }
                    h
                }
            };
            cand.1 = s;
        }
        // select
        let mut chosen: Vec<usize> = vec![];
        let mut idx: Vec<usize> = (0..cands.len()).collect();
        match cfg.engine.as_str() {
            "saturate" => chosen = idx.clone(),
            "greedy" => {
                idx.sort_by_key(|&i| cands[i].1);
                chosen = idx.into_iter().take(cfg.beam).collect();
            }
            _ => {
                idx.sort_by(|&a, &b| {
                    cands[a].1.cmp(&cands[b].1).then(
                        ctx.stats.ucb(cands[b].0.rule).partial_cmp(&ctx.stats.ucb(cands[a].0.rule)).unwrap())
                });
                let exploit = if cfg.bridge { (cfg.beam * 4) / 5 } else { cfg.beam };
                for &i in idx.iter().take(exploit) {
                    chosen.push(i);
                }
                if cfg.bridge {
                    let mut rest: Vec<usize> = idx.iter().copied().skip(exploit).collect();
                    rest.sort_by_key(|&i| {
                        let key = (cands[i].0.rule, eg.nodes[cands[i].0.node as usize].op);
                        (*visits.get(&key).unwrap_or(&0), -cands[i].1)
                    });
                    for i in rest.into_iter().take(cfg.beam - exploit) {
                        chosen.push(i);
                    }
                }
            }
        }
        // apply
        let mut merged_any = false;
        let mut collision_prov: Vec<u32> = vec![];
        let nodes_before = eg.nodes.len();
        let mut grew_without_merge = vec![false; NRULES];
        let mut fired = vec![false; NRULES];
        for &i in &chosen {
            if alloc <= 0 {
                break;
            }
            let m = &cands[i].0;
            let prem_prov: Vec<u32> = m.premises.iter().map(|&n| prov.get(n)).collect();
            let prem_depth = m.premises.iter().map(|&n| *depthv.get(n as usize).unwrap_or(&0)).max().unwrap_or(0);
            let nd = prem_depth + 1;
            if cfg.depthfuel && nd > cfg.depth {
                continue;
            }
            let mut fr = vec![];
            let built = build(&mut eg, &m.rhs, &mut fr, alloc);
            let Some((rc, rn)) = built else { alloc = 0; break; };
            alloc -= fr.len() as i64;
            out.alloc_used += fr.len() as i64;
            for &f in &fr {
                if depthv.len() <= f as usize {
                    depthv.resize(f as usize + 1, 0);
                }
                depthv[f as usize] = nd;
            }
            let bridge = cands[i].1 > h_before && cfg.engine == "witness";
            let pid = if cfg.prov {
                let mut last = BASE;
                for &f in &fr {
                    last = prov.record(f, m.rule as u16, &prem_prov, bridge);
                }
                if fr.is_empty() {
                    last = prov.record(rn, m.rule as u16, &prem_prov, bridge);
                }
                last
            } else {
                BASE
            };
            fired[m.rule] = true;
            visits.entry((m.rule, eg.nodes[m.node as usize].op)).and_modify(|v| *v += 1).or_insert(1);
            used.insert(m.rule);
            let was = eg.find(m.class);
            if eg.union(m.class, rc) {
                if fr.is_empty() {
                    merged_any = true;
                }
                last_merge_prov.insert(eg.find(was), pid);
                collision_prov.push(pid);
            } else if !fr.is_empty() {
                grew_without_merge[m.rule] = true;
            }
            ctx.stats.n[m.rule] += 1.0;
            ctx.stats.total += 1.0;
        }
        // congruence closure, recorded as RULE_CONG derivations that link
        // the outer merge back to the inner merge that caused it
        {
            let before = eg.match_steps;
            let congs = eg.rebuild();
            if cfg.prov {
                for (p, q) in congs {
                    let kidmerge = eg.nodes[p as usize].kids.iter()
                        .filter_map(|k| last_merge_prov.get(&eg.find(*k)).copied()).next().unwrap_or(BASE);
                    let pp = prov.get(q);
                    let id = prov.record(p, RULE_CONG, &[pp, kidmerge], false);
                    last_merge_prov.insert(eg.find(eg.node_class[p as usize]), id);
                    collision_prov.push(id);
                }
            }
            let st = (eg.match_steps - before) as i64;
            matchf -= st;
            out.match_used += st;
        }
        eg.extract();
        let h_after = hroot(&eg, cfg.bidir);
        let progress = h_after < h_before || eg.find(cs) == eg.find(cw) || merged_any;
        // backoff for greedy (and witness without credit)
        if cfg.engine == "greedy" || (cfg.engine == "witness" && !cfg.credit) {
            for r in 0..NRULES {
                if fired[r] && grew_without_merge[r] && !progress {
                    ctx.stats.ban_k[r] = (ctx.stats.ban_k[r] + 1).min(10);
                    ctx.stats.ban_until[r] = round + (1usize << ctx.stats.ban_k[r]);
                }
            }
        }
        if progress && h_after < h_before {
            let reward = (h_before - h_after) as f64 * if eg.find(cs) == eg.find(cw) && cfg.bidir { 2.0 } else { 1.0 };
            if cfg.prov && cfg.credit {
                credit_walk(&prov, &collision_prov, reward, &mut delta, &mut out.walk_steps,
                            &mut out.double_credit, !cfg.prov_naive, &mut out.cong_credit_to_bridge);
            }
            if cfg.dividend && cap > 0 {
                let spent = (eg.nodes.len() - nodes_before) as i64 + spent_match;
                let refund = (spent / 2).min(cap);
                cap -= refund;
                alloc += refund / 2;
                matchf += refund - refund / 2;
                out.refunded += refund;
            }
        }
        h_before = h_after;
        if cfg.engine == "saturate" && eg.nodes.len() == nodes_before && !merged_any {
            out.status = "fixpoint";
            break;
        }
    }
    if eg.find(cs) == eg.find(cw) {
        out.status = "proved";
    }
    // flush epoch credit into the global table, then drop the arena
    for r in 0..NRULES {
        ctx.stats.credit[r] += delta[r];
    }
    out.enodes = eg.nodes.len();
    out.classes = eg.classes().len();
    out.prov_nodes = prov.nodes.len() - 1;
    out.prov_bytes = prov.bytes();
    out.prov_acyclic = prov.acyclic();
    out.rules_used = used.into_iter().collect();
    out.rules_used.sort();
    if out.status == "proved" {
        // independent check on fresh points: rules must be sound
        let before = evals_now();
        let mut vs = vec![];
        vars(src, &mut vs);
        vars(wit, &mut vs);
        for p in points(&vs, 64, 0xFEED) {
            if eval(src, &p) != eval(wit, &p) {
                out.verified = false;
            }
        }
        EVALS.fetch_sub(evals_now() - before, std::sync::atomic::Ordering::Relaxed);
    }
    out.micros = t0.elapsed().as_micros();
    out
}

fn au_terms(a: &T, b: &T) -> i64 {
    if a.op == b.op && a.kids.len() == b.kids.len() {
        a.kids.iter().zip(&b.kids).map(|(x, y)| au_terms(x, y)).sum()
    } else if a == b {
        0
    } else {
        (size(a) + size(b)) as i64
    }
}

/// Exhaustive evaluation over the resolved witness points: the
/// observer-applied join at this resolution is decided exactly.
fn run_eval(src: &T, wit: &T, pts: &[HashMap<u32, i64>]) -> Outcome {
    let t0 = Instant::now();
    let mut eq = true;
    let mut used = 0;
    for p in pts {
        used += 1;
        if eval(src, p) != eval(wit, p) {
            eq = false;
            break;
        }
    }
    let _ = used;
    // audit, not counted: does a bounded join also hold on 64 fresh points?
    let mut verified = true;
    if eq {
        let before = evals_now();
        let mut vs = vec![];
        vars(src, &mut vs);
        vars(wit, &mut vs);
        for p in points(&vs, 64, 0xFEED) {
            if eval(src, &p) != eval(wit, &p) {
                verified = false;
            }
        }
        EVALS.fetch_sub(evals_now() - before, std::sync::atomic::Ordering::Relaxed);
    }
    Outcome {
        status: if eq { "agree" } else { "refuted" }, rounds: 0, alloc_used: 0, match_used: 0,
        refunded: 0, enodes: 0, classes: 0, prov_nodes: 0, prov_bytes: 0, prov_acyclic: true, walk_steps: 0,
        double_credit: 0, cong_credit_to_bridge: 0.0, micros: t0.elapsed().as_micros(), verified, rules_used: vec![], evals: 0,
    }
}

// one operator applied to its children's values: the same semantics
// as eval, node by node
fn apply(op: Op, k: &[i64], env: &HashMap<u32, i64>) -> i64 {
    EVALS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    match op {
        Op::Var(s) => *env.get(&s).unwrap_or(&((mix(s as u64) as i64) & 0xff)),
        Op::Const(c) => c,
        Op::Add => k[0].wrapping_add(k[1]),
        Op::Mul => k[0].wrapping_mul(k[1]),
        Op::Sub => k[0].wrapping_sub(k[1]),
        Op::Neg => k[0].wrapping_neg(),
        Op::Shl => k[0].wrapping_shl((k[1] & 63) as u32),
        Op::Shr => k[0].wrapping_shr((k[1] & 63) as u32),
        Op::Div => if k[1] == 0 { 0 } else { k[0].wrapping_div_euclid(k[1]) },
        Op::Mod => if k[1] == 0 { 0 } else { k[0].wrapping_rem_euclid(k[1]) },
        Op::And => k[0] & k[1],
        Op::Or => k[0] | k[1],
        Op::Xor => k[0] ^ k[1],
        Op::Idx(s) => (mix((s as u64) << 32 ^ (k[0] as u64)) & 0xffff) as i64,
        Op::Call(s) => {
            let mut h = mix(s as u64 ^ 0xC0FFEE);
            for &v in k {
                h = mix(h ^ (v as u64));
            }
            (h & 0xffff) as i64
        }
    }
}

// The bounded decider. Both terms go into one hash-consed DAG, so a
// subterm the two sides share is evaluated once per point; identical
// roots join with no evaluation at all. Then every resolved point is
// evaluated bottom-up, stopping at the first point where the roots
// differ. Joined exactly when the roots agree on every point, which is
// the graph's equivalence inside the bound (boundedexact); no sound
// engine joins a pair this refutes (decidermax, decidercovers).
fn run_decide(src: &T, wit: &T, pts: &[HashMap<u32, i64>]) -> Outcome {
    let t0 = Instant::now();
    let mut ids: HashMap<(Op, Vec<u32>), u32> = HashMap::new();
    let mut nodes: Vec<(Op, Vec<u32>)> = vec![];
    fn intern(t: &T, ids: &mut HashMap<(Op, Vec<u32>), u32>, nodes: &mut Vec<(Op, Vec<u32>)>) -> u32 {
        let ks: Vec<u32> = t.kids.iter().map(|k| intern(k, ids, nodes)).collect();
        let key = (t.op, ks);
        if let Some(&i) = ids.get(&key) {
            return i;
        }
        let i = nodes.len() as u32;
        nodes.push(key.clone());
        ids.insert(key, i);
        i
    }
    let ra = intern(src, &mut ids, &mut nodes);
    let rb = intern(wit, &mut ids, &mut nodes);
    let mut eq = true;
    if ra != rb {
        let mut val = vec![0i64; nodes.len()];
        let mut kv: Vec<i64> = vec![];
        'pts: for p in pts {
            for i in 0..nodes.len() {
                kv.clear();
                for &c in &nodes[i].1 {
                    kv.push(val[c as usize]);
                }
                val[i] = apply(nodes[i].0, &kv, p);
            }
            if val[ra as usize] != val[rb as usize] {
                eq = false;
                break 'pts;
            }
        }
    }
    let mut verified = true;
    if eq {
        let before = evals_now();
        let mut vs = vec![];
        vars(src, &mut vs);
        vars(wit, &mut vs);
        for p in points(&vs, 64, 0xFEED) {
            if eval(src, &p) != eval(wit, &p) {
                verified = false;
            }
        }
        EVALS.fetch_sub(evals_now() - before, std::sync::atomic::Ordering::Relaxed);
    }
    Outcome {
        status: if eq { "agree" } else { "refuted" }, rounds: 0, alloc_used: 0, match_used: 0,
        refunded: 0, enodes: nodes.len(), classes: 0, prov_nodes: 0, prov_bytes: 0, prov_acyclic: true, walk_steps: 0,
        double_credit: 0, cong_credit_to_bridge: 0.0, micros: t0.elapsed().as_micros(), verified, rules_used: vec![], evals: 0,
    }
}

fn parse_cfg(args: &[String]) -> Cfg {
    let mut c = Cfg {
        engine: "witness".into(), beh: true, au: true, bag: true, lin: true, ent: true, bidir: true, bridge: true,
        credit: true, dividend: true, depthfuel: true, prov: true, prov_naive: false, use_credit_for_sched: true,
        alloc: 400, matchf: 4000, depth: 12, cap: 2000, beam: 10, quota: 128, rules: base_rules(false),
        npoints: 64, rounds: 400, label: String::new(),
    };
    let mut i = 0;
    while i < args.len() {
        let a = args[i].as_str();
        let mut val = || { i += 1; args[i].clone() };
        match a {
            "--engine" => c.engine = val(),
            "--label" => c.label = val(),
            "--no-beh" => c.beh = false,
            "--no-au" => c.au = false,
            "--no-bag" => c.bag = false,
            "--no-lin" => c.lin = false,
            "--no-linrule" => c.rules[R_LIN] = false,
            "--no-ent" => c.ent = false,
            "--uni" => c.bidir = false,
            "--no-bridge" => c.bridge = false,
            "--no-credit" => c.credit = false,
            "--no-dividend" => c.dividend = false,
            "--no-depth" => c.depthfuel = false,
            "--no-prov" => { c.prov = false; }
            "--prov-naive" => c.prov_naive = true,
            "--record-only" => c.use_credit_for_sched = false,
            "--gen" => c.rules[R_GEN] = true,
            "--with-beh" => {}
            "--alloc" => c.alloc = val().parse().unwrap(),
            "--match" => c.matchf = val().parse().unwrap(),
            "--depth" => c.depth = val().parse().unwrap(),
            "--cap" => c.cap = val().parse().unwrap(),
            "--beam" => c.beam = val().parse().unwrap(),
            "--quota" => c.quota = val().parse().unwrap(),
            "--no-acrule" => c.rules[R_ACNORM] = false,
            "--points" => c.npoints = val().parse().unwrap(),
            "--rounds" => c.rounds = val().parse().unwrap(),
            other => panic!("unknown flag {}", other),
        }
        i += 1;
    }
    match c.engine.as_str() {
        "greedy" => {
            // plain greedy with backoff: no witness-side machinery; it gets
            // the witness engine's whole ceiling (budget plus dividend cap)
            c.beh = false; c.au = false; c.bag = false; c.lin = false; c.ent = false; c.bidir = false;
            c.bridge = false; c.credit = false; c.dividend = false;
            c.alloc += c.cap / 2; c.matchf += c.cap - c.cap / 2; c.cap = 0;
        }
        "saturate" => {
            c.beh = false; c.au = false; c.bag = false; c.lin = false; c.ent = false; c.bidir = false;
            c.bridge = false; c.credit = false; c.dividend = false; c.depthfuel = false;
            c.alloc += c.cap / 2; c.matchf += c.cap - c.cap / 2; c.cap = 0;
        }
        _ => {}
    }
    // after engine defaults: a baseline may be given the witness points
    if args.iter().any(|a| a == "--with-beh") {
        c.beh = true;
    }
    c
}

fn main() {
    assert_eq!(std::mem::size_of::<ProvNode>(), 16, "ProvNode must be 16 bytes");
    let args: Vec<String> = std::env::args().skip(1).collect();
    let cfg = parse_cfg(&args);
    let mut stats = RuleStats::new();
    let stdin = io::stdin();
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let f: Vec<&str> = line.split('\t').collect();
        let (id, suite, s, w) = (f[0], f[1], f[2], f[3]);
        let (src, wit) = (parse_str(s), parse_str(w));
        let mut vs = vec![];
        vars(&src, &mut vs);
        vars(&wit, &mut vs);
        let pts = points(&vs, cfg.npoints, 0x5EED);
        let e0 = evals_now();
        let mut o = if cfg.engine == "eval" {
            run_eval(&src, &wit, &pts)
        } else if cfg.engine == "decide" {
            run_decide(&src, &wit, &pts)
        } else {
            let mut ctx = Ctx { cfg: &cfg, stats: &mut stats };
            run_witness(&src, &wit, &mut ctx, &pts)
        };
        o.evals = evals_now() - e0;
        let ru: Vec<String> = o.rules_used.iter().map(|&r| format!("\"{}\"", RULE_NAMES[r])).collect();
        println!(
            "{{\"id\":\"{}\",\"suite\":\"{}\",\"engine\":\"{}\",\"label\":\"{}\",\"status\":\"{}\",\"rounds\":{},\"alloc\":{},\"match\":{},\"refunded\":{},\"enodes\":{},\"classes\":{},\"prov_nodes\":{},\"prov_bytes\":{},\"prov_acyclic\":{},\"walk_steps\":{},\"double_credit\":{},\"cong_bridge_credit\":{:.4},\"micros\":{},\"verified\":{},\"evals\":{},\"rules\":[{}]}}",
            id, suite, cfg.engine, cfg.label, o.status, o.rounds, o.alloc_used, o.match_used, o.refunded, o.enodes, o.classes,
            o.prov_nodes, o.prov_bytes, o.prov_acyclic, o.walk_steps, o.double_credit, if o.cong_credit_to_bridge.is_finite() { o.cong_credit_to_bridge.min(1e12) } else { -1.0 }, o.micros,
            o.verified, o.evals, ru.join(",")
        );
    }
    // peak resident memory of this process (Linux)
    let hwm = std::fs::read_to_string("/proc/self/status").ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).map(|l| l.to_string()))
        .and_then(|l| l.split_whitespace().nth(1).map(|x| x.to_string()))
        .unwrap_or_else(|| "0".into());
    println!("{{\"summary\":true,\"vmhwm_kb\":{}}}", hwm);
}

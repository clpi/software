namespace SoftwareDoesntRegress

inductive Kind where
  | symbol
  | context
  | data
  | configuration
  | deployment
  deriving DecidableEq, Repr

inductive Cone (deps : List (Nat × Nat)) (changed : List Nat) : Nat → Prop where
  | seed {n : Nat} : n ∈ changed → Cone deps changed n
  | step {user dep : Nat} : (user, dep) ∈ deps → Cone deps changed dep → Cone deps changed user

def symbolSeeds (kind : Nat → Kind) (changed : List Nat) : List Nat :=
  changed.filter fun n => decide (kind n = Kind.symbol)

def symbolDeps (kind : Nat → Kind) (deps : List (Nat × Nat)) : List (Nat × Nat) :=
  deps.filter fun e => decide (kind e.1 = Kind.symbol) && decide (kind e.2 = Kind.symbol)

theorem cone_empty {s : Nat} : ¬ Cone [] [] s := by
  intro h
  cases h with
  | seed hs => simp at hs
  | step hdep _ => simp at hdep

theorem unchanged_symbol_context_recheck {kind : Nat → Kind} {deps : List (Nat × Nat)}
    {changed : List Nat} {s c : Nat}
    (hs : kind s = Kind.symbol) (hc : kind c = Kind.context)
    (hun : s ∉ changed) (hchg : c ∈ changed) (hedge : (s, c) ∈ deps) :
    Cone deps changed s ∧ s ∉ changed ∧ kind s = Kind.symbol ∧ kind c = Kind.context :=
  ⟨Cone.step hedge (Cone.seed hchg), hun, hs, hc⟩

def inertial : Nat := 0
def trajectory : Nat := 1

def arianeKind : Nat → Kind
  | 0 => Kind.symbol
  | 1 => Kind.context
  | _ => Kind.symbol

def arianeDeps : List (Nat × Nat) := [(inertial, trajectory)]
def arianeChanged : List Nat := [trajectory]

theorem ariane_symbol_seeds : symbolSeeds arianeKind arianeChanged = [] := by decide
theorem ariane_symbol_deps : symbolDeps arianeKind arianeDeps = [] := by decide

theorem ariane_symbol_only_misses :
    ¬ Cone (symbolDeps arianeKind arianeDeps) (symbolSeeds arianeKind arianeChanged) inertial := by
  rw [ariane_symbol_seeds, ariane_symbol_deps]
  exact cone_empty

theorem ariane_context_cone_catches : Cone arianeDeps arianeChanged inertial :=
  Cone.step (List.Mem.head _) (Cone.seed (List.Mem.head _))

def sensor : Nat := 2
def contentTemplate : Nat := 3

def crowdKind : Nat → Kind
  | 2 => Kind.symbol
  | 3 => Kind.data
  | _ => Kind.symbol

def crowdDeps : List (Nat × Nat) := [(sensor, contentTemplate)]
def crowdChanged : List Nat := [contentTemplate]

theorem crowd_symbol_seeds : symbolSeeds crowdKind crowdChanged = [] := by decide
theorem crowd_symbol_deps : symbolDeps crowdKind crowdDeps = [] := by decide

theorem crowdstrike_symbol_only_misses :
    ¬ Cone (symbolDeps crowdKind crowdDeps) (symbolSeeds crowdKind crowdChanged) sensor := by
  rw [crowd_symbol_seeds, crowd_symbol_deps]
  exact cone_empty

theorem crowdstrike_data_cone_catches : Cone crowdDeps crowdChanged sensor :=
  Cone.step (List.Mem.head _) (Cone.seed (List.Mem.head _))

def router : Nat := 4
def configFlag : Nat := 5
def rollout : Nat := 6

def knightKind : Nat → Kind
  | 4 => Kind.symbol
  | 5 => Kind.configuration
  | 6 => Kind.deployment
  | _ => Kind.symbol

def knightDeps : List (Nat × Nat) := [(router, configFlag), (router, rollout)]
def knightChanged : List Nat := [configFlag, rollout]

theorem knight_symbol_seeds : symbolSeeds knightKind knightChanged = [] := by decide
theorem knight_symbol_deps : symbolDeps knightKind knightDeps = [] := by decide

theorem knight_symbol_only_misses :
    ¬ Cone (symbolDeps knightKind knightDeps) (symbolSeeds knightKind knightChanged) router := by
  rw [knight_symbol_seeds, knight_symbol_deps]
  exact cone_empty

theorem knight_config_cone_catches : Cone knightDeps knightChanged router :=
  Cone.step (List.Mem.head _) (Cone.seed (List.Mem.head _))

theorem knight_deployment_cone_catches : Cone knightDeps knightChanged router :=
  Cone.step (List.Mem.tail _ (List.Mem.head _)) (Cone.seed (List.Mem.tail _ (List.Mem.head _)))

end SoftwareDoesntRegress

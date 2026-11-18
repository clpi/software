namespace IncrementalCert

structure Profile (ω : Type) where
  obs : ω → Prop

def profileLE {ω : Type} (p q : Profile ω) : Prop :=
  ∀ o, p.obs o → q.obs o

inductive Reaches {σ ω : Type} (deps : σ → σ → Prop) (B : σ → Profile ω) :
    σ → ω → Prop where
  | here {s : σ} {o : ω} : (B s).obs o → Reaches deps B s o
  | step {s t : σ} {o : ω} : deps s t → Reaches deps B t o → Reaches deps B s o

def allowedTrace {ω : Type} (A : ω → Prop) (t : List ω) : Prop :=
  ∀ o, o ∈ t → A o

theorem unordered_traces {ω : Type} (A : ω → Prop) {t1 t2 : List ω}
    (h : List.Perm t1 t2) : allowedTrace A t1 ↔ allowedTrace A t2 := by
  constructor
  · intro ht o ho
    exact ht o ((List.Perm.mem_iff h).mpr ho)
  · intro ht o ho
    exact ht o ((List.Perm.mem_iff h).mp ho)

def flowBeh : String → Profile String :=
  fun s => if s = "lib" then ⟨fun o => o = "secret"⟩ else ⟨fun _ => False⟩

def flowDeps : String → String → Prop :=
  fun a b => a = "app" ∧ b = "lib"

def noDeps : String → String → Prop :=
  fun _ _ => False

theorem profile_cannot_see_flow :
    Reaches flowDeps flowBeh "app" "secret" ∧
      ¬ Reaches noDeps flowBeh "app" "secret" := by
  refine ⟨?_, ?_⟩
  · have hlib : (flowBeh "lib").obs "secret" := by simp [flowBeh]
    exact Reaches.step (by simp [flowDeps]) (Reaches.here hlib)
  · intro h
    cases h with
    | here hobs => simp [flowBeh] at hobs
    | step hdep _ => simp [noDeps] at hdep

end IncrementalCert

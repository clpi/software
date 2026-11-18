import Certificate

namespace FrameCampaign

-- The command is a nibble; the second nibble must be its one's complement.
abbrev Frame := Nat × Nat
def decode (f : Frame) : Option Nat :=
  if f.1 < 16 ∧ f.2 < 16 ∧ f.1 + f.2 = 15 then some f.1 else none
def encode (cmd : Nat) : Frame := (cmd,15-cmd)
def raw := (List.range 16).flatMap fun a => (List.range 16).map fun b => (a,b)
def directed := (List.range 16).map encode
def seen (fs : List Frame) := fs.filterMap decode

theorem invertible (f : Frame) (n : Nat) :
    decode f = some n ↔ n < 16 ∧ f = encode n := by
  rcases f with ⟨a,b⟩
  simp only [decode,encode,Prod.mk.injEq]
  split <;> simp_all <;> omega

set_option maxRecDepth 2048 in
theorem exact_campaign : seen raw = List.range 16 ∧ seen directed = seen raw ∧
    raw.length = 256 ∧ directed.length = 16 := by decide

def asPlan (fs : List Frame) : Fuzzing.FinitePlan 16 :=
  ⟨⟨1,1,1,1⟩, fun n => (seen fs).contains n.val, fs.length⟩

theorem accepted_certificate : Fuzzing.certify (asPlan directed) (asPlan raw) = true := by
  apply (Fuzzing.certify_exact _ _).mpr
  obtain ⟨_,same,oldCost,newCost⟩ := exact_campaign
  exact ⟨rfl, ⟨fun i hi => by simpa only [Fuzzing.FinitePlan.summary, asPlan, same] using hi,
    by change directed.length ≤ raw.length; omega⟩,
    by change directed.length < raw.length; omega⟩

private theorem slots (n : Nat) (xs : List Nat) (allSeen : ∀ i < n, i ∈ xs) :
    n ≤ xs.length := by
  induction n generalizing xs with
  | zero => omega
  | succ n ih =>
    have hn := allSeen n (by omega)
    have rest := ih (xs.erase n) (fun i hi => (List.mem_erase_of_ne (Nat.ne_of_lt hi)).mpr
      (allSeen i (by omega)))
    rw [List.length_erase_of_mem hn] at rest
    have pos := List.length_pos_of_mem hn
    omega

theorem minimum_invocations (fs : List Frame) (covers : ∀ n < 16, n ∈ seen fs) :
    directed.length ≤ fs.length := by
  change 16 ≤ fs.length
  exact Nat.le_trans (slots 16 _ covers) (List.length_filterMap_le ..)

-- Expanding the contract to include rejection makes the directed campaign insufficient.
theorem rejection_boundary : raw.any (fun f => (decode f).isNone) = true ∧
    directed.any (fun f => (decode f).isNone) = false := by decide

#eval (raw.length, directed.length, seen directed)
#print axioms invertible
#print axioms exact_campaign
#print axioms accepted_certificate
#print axioms minimum_invocations
#print axioms rejection_boundary
end FrameCampaign

import Std

namespace RangeLedger.IntervalCampaign
abbrev Span := Nat × Nat
abbrev Tag := Option (Nat × Nat)
def classify (span : Span) : Tag :=
  if span.1 = span.2 then none else some (span.1/16,(span.2-1)/16)
def encode : Tag → Span
  | none => (0,0)
  | some (i,j) => (16*i,16*j+1)
def tags : List Tag := none :: (List.range 4).flatMap (fun i =>
  ((List.range 4).filter (fun j => i ≤ j)).map (fun j => some (i,j)))
def raw : List Span := (List.range 65).flatMap (fun a =>
  ((List.range 65).filter (fun b => a ≤ b)).map (fun b => (a,b)))

theorem representable (a b : Nat) (ab : a ≤ b) (bound : b ≤ 64) :
    classify (a,b) ∈ tags := by
  by_cases e : a = b
  · simp [classify,e,tags]
  · have lo : a/16 < 4 := by omega
    have hi : (b-1)/16 < 4 := by omega
    have ord : a/16 ≤ (b-1)/16 := by omega
    simp only [classify,if_neg e,tags,List.mem_cons,List.mem_flatMap,List.mem_map]
    exact Or.inr ⟨a/16,List.mem_range.mpr lo,(b-1)/16, by simp [hi,ord],rfl⟩

theorem round_trip (t : Tag) (h : t ∈ tags) : classify (encode t) = t := by
  cases t with
  | none => rfl
  | some v =>
    obtain ⟨i,j⟩ := v
    simp [tags] at h
    simp [classify,encode]; omega

theorem legal_representative (t : Tag) (h : t ∈ tags) :
    (encode t).1 ≤ (encode t).2 ∧ (encode t).2 ≤ 64 := by
  cases t with
  | none => decide
  | some v =>
    obtain ⟨i,j⟩ := v
    simp [tags] at h
    simp [encode]; omega

private theorem covered_size (ts ss : List Tag) (u : ts.Nodup) (covers : ∀ t ∈ ts, t ∈ ss) :
    ts.length ≤ ss.length := by
  induction ts generalizing ss with
  | nil => simp
  | cons t ts ih =>
    have h := covers t (by simp)
    obtain ⟨fresh,unique⟩ := List.nodup_cons.mp u
    have small := ih (ss.erase t) unique (fun x hx =>
      (List.mem_erase_of_ne (show x ≠ t from fun e => fresh (e ▸ hx))).mpr (covers x (by simp [hx])))
    rw [List.length_erase_of_mem h] at small
    have pos := List.length_pos_of_mem h
    simp only [List.length_cons]; omega

theorem minimum (fs : List Span) (covers : ∀ t ∈ tags, t ∈ fs.map classify) :
    11 ≤ fs.length := by
  have floor := covered_size tags (fs.map classify) (by decide) covers
  change 11 ≤ (fs.map classify).length at floor
  simpa using floor

theorem count : tags.length = 11 := by decide
theorem boundary : classify (0,1) = classify (0,16) ∧ (1 : Nat) ≠ 16 := by decide
#eval (raw.length,tags.length)
#print axioms representable
#print axioms round_trip
#print axioms legal_representative
#print axioms minimum
#print axioms boundary
end RangeLedger.IntervalCampaign

import SoftwareDoesntNeedReview.Mechanize
import SoftwareDoesntNeedReview.Chain

namespace SoftwareDoesntNeedReview

namespace Replacement

open Mechanize

def dispositions : List Criterion → List Outcome
  | [] => []
  | c :: cs => dispose c :: dispositions cs

theorem process_terminates :
    ∀ cs : List Criterion, (dispositions cs).length = cs.length
  | [] => rfl
  | _ :: cs => by simp [dispositions, process_terminates cs]

def watchedOf : List Criterion → List (Sym × Ax)
  | [] => []
  | Criterion.profile s a :: cs => (s, a) :: watchedOf cs
  | Criterion.semantic _ :: cs => watchedOf cs
  | Criterion.approx _ s a _ :: cs => (s, a) :: watchedOf cs

def premisesOf : List Criterion → List String
  | [] => []
  | Criterion.semantic n :: cs => n :: premisesOf cs
  | _ :: cs => premisesOf cs

def gapsOf : List Criterion → List String
  | [] => []
  | Criterion.approx _ _ _ g :: cs => g :: gapsOf cs
  | _ :: cs => gapsOf cs

theorem semantic_adds_no_watch (n : String) (cs : List Criterion) :
    watchedOf (Criterion.semantic n :: cs) = watchedOf cs := rfl

theorem watched_grows :
    ∀ (extra cs : List Criterion) (s : Sym) (a : Ax),
      watchedHas (watchedOf cs) s a = true →
        watchedHas (watchedOf (cs ++ extra)) s a = true
  | _, [], _, _, h => by simp [watchedOf, watchedHas] at h
  | extra, Criterion.profile s' a' :: cs, s, a, h => by
    have hgrow := watched_grows extra cs s a
    simp [watchedOf, List.cons_append, watchedHas, Bool.or_eq_true] at h ⊢
    cases h with
    | inl hhead => exact Or.inl hhead
    | inr htail => exact Or.inr (hgrow htail)
  | extra, Criterion.semantic n :: cs, s, a, h => by
    simpa [watchedOf, List.cons_append] using watched_grows extra cs s a h
  | extra, Criterion.approx n s' a' g :: cs, s, a, h => by
    have hgrow := watched_grows extra cs s a
    simp [watchedOf, List.cons_append, watchedHas, Bool.or_eq_true] at h ⊢
    cases h with
    | inl hhead => exact Or.inl hhead
    | inr htail => exact Or.inr (hgrow htail)

theorem process_monotone (cs extra : List Criterion) (R : Release) (s : Sym) (a : Ax)
    (hw : watchedHas (watchedOf cs) s a = true)
    (hb : (behaviorAt R s a == some Status.bad) = true) :
    refusesCell (watchedOf (cs ++ extra)) R s a = true :=
  Chain.Certifiable.extensive (watchedOf cs) (watchedOf (cs ++ extra)) R s a
    (fun s' a' h => watched_grows extra cs s' a' h) hw hb

theorem criterion_never_lost (cs : List Criterion) (R : Release) (s : Sym) (a : Ax)
    (hw : watchedHas (watchedOf cs) s a = true)
    (hb : (behaviorAt R s a == some Status.bad) = true) :
    refusesCell (watchedOf cs) R s a = true :=
  Chain.Certifiable.extensive (watchedOf cs) (watchedOf cs) R s a (fun _ _ h => h) hw hb

end Replacement

end SoftwareDoesntNeedReview

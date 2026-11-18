# Proposal

Human review of a code diff is removed only for a change inside the narrow theorem: the impact lies in a sound cone (`ClosureHyp`, the context-aware call closure), and the spec, roots, and rules are unchanged. For the machine-checked property, rechecking that cone is the review. The review bit adds nothing beyond the certifier.

Human attention moves to what certification cannot discharge. `Qualification.soundness` needs `validRoots` and `validRules`. A wrong spec, a missing requirement, or a wrong allow-list is a failure of those premises. The Mars Climate Orbiter boundary is an opaque token the allow-list treats as one unit while the two sides denote pound-force seconds and newton seconds. The MCAS boundary is a rule that one angle-of-attack sensor is enough. In both, the certifier accepts and only a review of the spec rejects.

What remains for a person:

- the spec
- the roots
- the rules
- qualification of the dependency analysis that computes the cone, in the style of DO-330 tool qualification

That qualification is of the analysis, not a second reading of a diff already inside a qualified cone. Nothing here says how often reviewers rubber-stamp, and nothing here says review is redundant once a certifier has run.

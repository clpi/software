import SoftwareIsComposable.Admission

namespace SoftwareIsComposable

def worseOld : Release :=
  { symbols := [
      { id := 1, behaviors := [0, 1], costs := [{ lo := 0, hi := 2 }, { lo := 1, hi := 4 }] },
      { id := 7, behaviors := [3], costs := [{ lo := 1, hi := 4 }] }] }

def worseNew : Release :=
  { symbols := [
      { id := 1, behaviors := [0, 1, 2], costs := [{ lo := 0, hi := 2 }, { lo := 1, hi := 3 }] },
      { id := 7, behaviors := [3], costs := [{ lo := 1, hi := 9 }] }] }

theorem worse_refused :
    symbolVerdicts worseOld worseNew =
      [(1, .admitted), (7, .refused (.costRegressed 7 0))] := by
  decide

theorem example_refused :
    releaseAdmitted worseOld worseNew = false := by
  decide

end SoftwareIsComposable

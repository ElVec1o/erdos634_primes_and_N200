import Erdos634.WordCount

namespace Erdos634.Draft.WordCountWrap
open Erdos634.WordCount

theorem wrap_missing_from_search :
    (1, 35, 0) ∈ baseWords 30 11 36 415 ∧ (2, 29, 1) ∈ baseWords 30 11 36 415
      ∧ (12, 5, 0) ∈ baseWords 30 11 36 415 :=
  missing_from_search

example : True := trivial
#check @wrap_missing_from_search

end Erdos634.Draft.WordCountWrap

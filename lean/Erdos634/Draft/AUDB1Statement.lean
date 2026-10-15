-- Prints the two statements in full and computes the
-- statement-relevant definitional closure (constants reachable from the TYPE of each theorem,
-- descending through bodies of defs/inductives/structures but never through theorem proofs).
-- Not imported by `All`.  No sorry, no native_decide.
import Erdos634.Draft.PrimeCharacterization
open Lean Elab Command Meta

namespace Erdos634.AUDB1

partial def stmtClosure (env : Environment) (roots : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack := roots
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      -- theorems: record, do not descend (proof content is irrelevant to MEANING)
      let isThm := match ci with | .thmInfo _ => true | _ => false
      if isThm then continue
      -- type always
      for c in ci.type.getUsedConstantsAsSet.toList do
        if !seen.contains c then stack := stack.push c
      -- value for defs
      match ci with
      | .defnInfo d =>
        for c in d.value.getUsedConstantsAsSet.toList do
          if !seen.contains c then stack := stack.push c
      | .inductInfo i =>
        for ctor in i.ctors do
          if !seen.contains ctor then stack := stack.push ctor
      | _ => pure ()
  return seen

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let env ← getEnv
  let mods := env.header.moduleNames
  let t1 := (env.find? `Erdos634.Draft.TheoremP6.theoremP_6).get!.type.getUsedConstantsAsSet.toArray
  let t2 := (env.find? `Erdos634.Draft.PrimeCharacterization.prime_tile_count_iff).get!.type.getUsedConstantsAsSet.toArray
  let r := stmtClosure env (t1 ++ t2)
  let mut userDefs : Array String := #[]
  let mut nonUser : Nat := 0
  let mut userThm : Array String := #[]
  for n in r.toList do
    let some ci := env.find? n | continue
    let modn := match env.getModuleIdxFor? n with | some i => mods[i.toNat]!.toString | none => "<current>"
    let isThm := match ci with | .thmInfo _ => true | _ => false
    if modn.startsWith "Erdos634" then
      if isThm then userThm := userThm.push s!"{modn} {n}"
      else userDefs := userDefs.push s!"{modn} {n}"
    else nonUser := nonUser + 1
  logInfo m!"statement closure: total {r.size}; user non-theorem {userDefs.size}; user theorems-in-types {userThm.size}; non-user {nonUser}"
  for s in userDefs.qsort (· < ·) do logInfo m!"USERDEF {s}"
  for s in userThm.qsort (· < ·) do logInfo m!"USERTHM-IN-TYPE {s}"

end Erdos634.AUDB1

set_option pp.proofs true
#print Erdos634.Geometry.Plane
#print Erdos634.Geometry.Tri
#print Erdos634.Geometry.Tri.carrier
#print Erdos634.Geometry.Dissection
#print Erdos634.Geometry.Tri.Congruent
#print Erdos634.Geometry.CongruentDissection
#check @Erdos634.Draft.TheoremP6.theoremP_6
#print Erdos634.Draft.TheoremP6.theoremP_6
#check @Erdos634.Draft.PrimeCharacterization.prime_tile_count_iff
set_option pp.all true in
#check @Erdos634.Draft.TheoremP6.theoremP_6
#print axioms Erdos634.Draft.TheoremP6.theoremP_6
#print axioms Erdos634.Draft.PrimeCharacterization.prime_tile_count_iff

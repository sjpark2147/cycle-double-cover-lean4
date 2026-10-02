import CycleDoubleCover
import Lean.Util.CollectAxioms

/-!
# Proof dependency audit

This command examines every public project theorem and definition and rejects every axiom
except Lean's standard logical foundations. In particular, `sorryAx` and
native-evaluation axioms are rejected. The audit is a build check rather
than a mathematical assumption in any theorem.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut definitions : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "CycleDoubleCover." then
      match info with
      | .axiomInfo _ => throwError "Project axiom declared: {name}"
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
        match info with
        | .thmInfo _ => checked := checked + 1
        | _ => definitions := definitions + 1
        let axioms ← collectAxioms name
        let forbidden := axioms.filter fun ax =>
          ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
        unless forbidden.isEmpty do
          throwError "Unexpected axioms in {name}: {forbidden}"
      | _ => pure ()
  if checked = 0 then
    throwError "No project theorems were found by the axiom audit."
  logInfo m!"Axiom audit passed for {checked} project theorems and {definitions} definitions."

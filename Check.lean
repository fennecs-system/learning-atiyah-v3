import Atiyah
import Lean.Util.CollectAxioms

/- Audit every public declaration in the project namespace, transitively.
   Standard Lean foundations are allowed; sorryAx and custom axioms are not. -/
run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked := 0
  for (name, _) in env.constants.toList do
    if name.getRoot == `Atiyah && !name.isInternal then
      let axioms ← Lean.collectAxioms name
      let unexpected := axioms.filter (fun ax => !allowed.contains ax)
      unless unexpected.isEmpty do
        throwError "{name} depends on forbidden axioms: {unexpected}"
      checked := checked + 1
  if checked == 0 then
    throwError "No project declarations were audited"
  Lean.logInfo m!"Axiom audit passed for {checked} project declarations."

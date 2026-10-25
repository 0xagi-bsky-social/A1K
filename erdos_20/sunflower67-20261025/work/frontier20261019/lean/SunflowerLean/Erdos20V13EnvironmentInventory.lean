import SunflowerLean.Erdos20V13Final
import SunflowerLean.Erdos20AxiomAudit

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := moduleNames[idx.toNat]!
      if mod.toString.startsWith "SunflowerLean." then
        let kind := match info with
          | .thmInfo _ => "theorem"
          | .defnInfo _ => "definition"
          | .axiomInfo _ => "axiom"
          | .opaqueInfo _ => "opaque"
          | _ => "other"
        rows := rows.push (Json.mkObj [("name",toJson name.toString),("module",toJson mod.toString),("kind",toJson kind)])
  logInfo m!"ERDOS20_ENV_INVENTORY {Json.compress (Json.arr rows)}"

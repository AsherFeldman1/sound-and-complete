import Lean

/-!
# Audit commands (from the `CLAUDE.md` appendix)

* `#spec_surface thm`: every definition of this project that the statement of
  `thm` depends on. That is everything you must read to know what `thm` means.
* `#audit_axioms thm`: the axioms the proof of `thm` uses. `sorryAx` means the
  proof is not finished.

This is tooling only. None of the app's guarantees depend on it.
-/

open Lean Elab Command

/-- Definitions a theorem's statement mentions, followed through their bodies.
The proof is not followed. -/
partial def specSurface (env : Environment) (thm : Name) : NameSet :=
  let rec go (todo : List Name) (seen : NameSet) : NameSet :=
    match todo with
    | [] => seen
    | c :: rest =>
      if seen.contains c then go rest seen else
      let next := match env.find? c with
        | some (.defnInfo d) => d.type.getUsedConstants.toList ++ d.value.getUsedConstants.toList
        | some ci => ci.type.getUsedConstants.toList
        | none => []
      go (next ++ rest) (seen.insert c)
  match env.find? thm with
  | some ci => go ci.type.getUsedConstants.toList {}
  | none => {}

/-- The module `c` is defined in, if it is one of this project's modules. -/
def ownModule? (env : Environment) (c : Name) : Option Name :=
  match env.getModuleIdxFor? c with
  | none => some `current
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some m => if (`SoundAndComplete).isPrefixOf m then some m else none
    | none => none

/-- Hide names the compiler makes on its own (constructors, recursors,
instances, and so on), so the list shows only what a person wrote. -/
def isWrittenByHand (env : Environment) (c : Name) : Bool :=
  !c.isInternal && !Meta.isMatcherCore env c && !isAuxRecursor env c &&
  !(c.getString!.startsWith "inst") && c.getString! != "ctorIdx" &&
  match env.find? c with
  | some (.ctorInfo _) | some (.recInfo _) => false
  | _ => true

/-- `#spec_surface thm`: the definitions the statement of `thm` depends on,
split into the spec (what you must agree with) and the code being checked. -/
elab "#spec_surface " id:ident : command => do
  let env ← getEnv
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let names := (specSurface env thm).toList.filter (isWrittenByHand env)
  let tagged := names.filterMap fun c => (ownModule? env c).map (c, ·)
  let isCode (m : Name) :=
    m == `SoundAndComplete.Search || m == `SoundAndComplete.Checkers || m == `SoundAndComplete.App
  let spec := (tagged.filter (!isCode ·.2)).map (·.1.toString) |>.toArray.qsort (· < ·)
  let code := (tagged.filter (isCode ·.2)).map (·.1.toString) |>.toArray.qsort (· < ·)
  logInfo m!"{thm}\n  spec (review these): {spec.toList}\n  code (checked by the proof): {code.toList}"

/-- `#audit_axioms thm`: print the axioms `thm` depends on. -/
elab "#audit_axioms " id:ident : command => do
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms thm
  logInfo m!"{thm}: {axs.toList}"

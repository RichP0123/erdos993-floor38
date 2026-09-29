/- Off-plan memory experiment. Retained ConstantInfo objects are the original
   objects, including proof bodies. Missing names and missing theorem axiom-cache
   entries are fatal. This is a loader optimization, never independent evidence
   that the original imported proofs are valid. Their full receipt audit remains
   required. No new declaration is inserted by this loader. -/
module
import all Lean.Environment
import all Lean.Util.CollectAxioms
public import Lean

public section
open Lean

namespace ExactKernelSubenvironment

def stamp (s : String) : IO Unit := do
  IO.println s!"{← IO.monoMsNow} {s}"
  (← IO.getStdout).flush

def hashPart (n : Name) : Nat := (hash n).toNat % 2147483648

structure Index where
  modules : Array ModuleData
  starts : Array Nat
  entries : Array Nat

def buildIndex (modules : Array ModuleData) : IO Index := do
  let mut starts := #[0]
  let mut total := 0
  let mut extras := 0
  for data in modules do
    unless data.constNames.size == data.constants.size do
      throw <| IO.userError "Constant names and values have different lengths"
    total := total + data.constants.size
    extras := extras + data.extraConstNames.size
    starts := starts.push total
  unless total < 4294967296 do
    throw <| IO.userError "32-bit constant-index capacity exceeded"
  stamp s!"COMPACT_INDEX_COUNTS MODULES {modules.size} CONSTANTS {total} MAIN_IR_EXTRAS {extras}"
  let mut entries := Array.emptyWithCapacity total
  let mut global := 0
  for data in modules do
    for n in data.constNames do
      entries := entries.push (hashPart n * 4294967296 + global)
      global := global + 1
  stamp "COMPACT_INDEX_SORT_BEGIN"
  entries := entries.qsort (· < ·)
  stamp "COMPACT_INDEX_SORT_END"
  return { modules, starts, entries }

def Index.at (index : Index) (global : Nat) : IO (ConstantInfo × Nat) := do
  unless global < index.starts.back! do
    throw <| IO.userError "Constant-index out of bounds"
  let mut lo := 0
  let mut hi := index.modules.size
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if index.starts[mid]! ≤ global then lo := mid else hi := mid
  let data := index.modules[lo]!
  let localIndex := global - index.starts[lo]!
  unless localIndex < data.constants.size do
    throw <| IO.userError "Module-local constant-index out of bounds"
  let ci := data.constants[localIndex]!
  unless ci.name == data.constNames[localIndex]! do
    throw <| IO.userError "Original constant name/value mismatch"
  return (ci, lo)

/-- Hashes only narrow the candidates. Full names are compared. Duplicates are
    accepted only if they are the identical original object; otherwise fail. -/
unsafe def Index.lookup (index : Index) (name : Name) : IO (ConstantInfo × Nat) := do
  let key := hashPart name * 4294967296
  let mut lo := 0
  let mut hi := index.entries.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if index.entries[mid]! < key then lo := mid + 1 else hi := mid
  let mut found : Option (ConstantInfo × Nat) := none
  while lo < index.entries.size && index.entries[lo]! / 4294967296 == hashPart name do
    let candidate ← index.at (index.entries[lo]! % 4294967296)
    if candidate.1.name == name then
      if let some previous := found then
        unless ptrEq previous.1 candidate.1 do
          throw <| IO.userError s!"Unequal duplicate original ConstantInfo: {name}"
      else
        found := some candidate
    lo := lo + 1
  match found with
  | some result => return result
  | none => throw <| IO.userError s!"Required original constant not found: {name}"

def Index.containsName (index : Index) (name : Name) : IO Bool := do
  let key := hashPart name * 4294967296
  let mut lo := 0
  let mut hi := index.entries.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if index.entries[mid]! < key then lo := mid + 1 else hi := mid
  while lo < index.entries.size && index.entries[lo]! / 4294967296 == hashPart name do
    if (← index.at (index.entries[lo]! % 4294967296)).1.name == name then return true
    lo := lo + 1
  return false

unsafe structure VisitState where
  visited : PtrSet Expr := mkPtrSet
  names : NameHashSet := {}

/-- Unlike Expr.getUsedConstants, include the structure owner of projections. -/
unsafe def expressionNames (e : Expr) : Array Name := Id.run do
  let mut state : VisitState := {}
  let mut todo := #[e]
  while !todo.isEmpty do
    let current := todo.back!
    todo := todo.pop
    if state.visited.contains current then continue
    state := { state with visited := state.visited.insert current }
    match current with
    | .const n _ => state := { state with names := state.names.insert n }
    | .proj n _ b =>
      state := { state with names := state.names.insert n }
      todo := todo.push b
    | .forallE _ d b _ | .lam _ d b _ => todo := (todo.push d).push b
    | .letE _ t v b _ => todo := ((todo.push t).push v).push b
    | .app f a => todo := (todo.push f).push a
    | .mdata _ b => todo := todo.push b
    | _ => pure ()
  return state.names.toArray

/-- Traverse all kernel-relevant non-theorem bodies and metadata. Theorem values
    remain present in the retained CI; only the dependency walk stops there. -/
unsafe def dependencies (ci : ConstantInfo) : Array Name := Id.run do
  let mut names := expressionNames ci.type
  match ci with
  | .defnInfo v => names := names ++ expressionNames v.value ++ v.all.toArray
  | .opaqueInfo v => names := names ++ expressionNames v.value ++ v.all.toArray
  | .inductInfo v => names := names ++ v.all.toArray ++ v.ctors.toArray
  | .ctorInfo v => names := names.push v.induct
  | .recInfo v =>
    names := names ++ v.all.toArray
    for rule in v.rules do
      names := (names.push rule.ctor) ++ expressionNames rule.rhs
  | _ => pure ()
  return names

private def cachedAtOwner (cache : ExportedAxiomsState) (owner : Nat) (name : Name) : Option (Array Name) := do
  let entries ← cache.importedModuleEntries[owner]?
  let entry ← entries.binSearch (name, #[]) (fun a b => Name.quickLt a.1 b.1)
  return entry.2

unsafe def load (imports : Array Import) (seeds freshNames : Array Name) (opts : Options)
    (checkParity := false) : IO Environment := do
  stamp "EXACT_SUBENV_IMPORT_CORE_BEGIN"
  let (_, imported) ← importModulesCore imports (globalLevel := .private) |>.run
  stamp "EXACT_SUBENV_IMPORT_CORE_END"
  let modules := imported.moduleNames.filterMap (imported.moduleNameMap[·]?)
  let data ← modules.mapM fun mod => do
    let some d := mod.mainModule? | throw <| IO.userError "Missing original module data"
    return d
  let irData ← modules.mapM fun mod => do
    let some d := mod.interpData? .private | throw <| IO.userError "Missing original IR data"
    return d
  let index ← buildIndex data
  for name in freshNames.push `Floor38KernelAssembly.rejectedNegativeControl do
    if (← index.containsName name) then
      throw <| IO.userError s!"New declaration name already occurs in full original imports: {name}"
  stamp s!"FULL_ORIGINAL_INDEX_NEW_NAME_FRESHNESS_ACCEPTED {freshNames.size + 1}"
  let extensions ← mkInitialExtensionStates
  let importedExtensions ← setImportedEntries extensions data
  let irExtensions ← setImportedEntries extensions irData
  let baseKernel : Kernel.Environment := {
    constants := SMap.fromHashMap ({} : Std.HashMap Name ConstantInfo) false
    const2ModIdx := {}
    quotInit := !imports.isEmpty
    extensions := importedExtensions
    irBaseExts := irExtensions
    header := {
      trustLevel := 0, imports, moduleData := data, isModule := false
      modules := modules.map (·.toEffectiveImport)
      regions := modules.flatMap (·.parts.map (·.2)) ++ modules.filterMap (·.irData?.map (·.2))
    }
  }
  let baseEnv := Environment.ofKernelEnv baseKernel
  let old := exportedAxiomsExt.toEnvExtension.getState (asyncMode := .mainOnly) baseEnv
  let state ← exportedAxiomsExt.addImportedFn old.importedEntries { env := baseEnv, opts }
  let baseEnv := exportedAxiomsExt.toEnvExtension.setState (asyncMode := .mainOnly) baseEnv { old with state }
  let cache := exportedAxiomsExt.getState (asyncMode := .mainOnly) baseEnv
  let mut constants : Std.HashMap Name ConstantInfo := {}
  let mut owners : Std.HashMap Name ModuleIdx := {}
  let mut uncached : NameHashSet := {}
  let mut todo := seeds ++ #[``False, ``True.intro, ``Eq.refl]
  let mut cursor := 0
  let mut theoremCount := 0
  stamp "EXACT_DEPENDENCY_CLOSURE_BEGIN"
  while cursor < todo.size do
    let n := todo[cursor]!
    cursor := cursor + 1
    if constants.contains n then continue
    let (ci, owner) ← index.lookup n
    constants := constants.insert n ci
    owners := owners.insert n owner
    if ci.isTheorem then theoremCount := theoremCount + 1
    todo := todo ++ dependencies ci
    if let .thmInfo thmVal := ci then
      if (cachedAtOwner cache owner n).isNone then
        uncached := uncached.insert n
        todo := todo ++ expressionNames thmVal.value
    if constants.size % 10000 == 0 then
      stamp s!"EXACT_DEPENDENCY_CLOSURE_PROGRESS {constants.size} PENDING {todo.size - cursor}"
  stamp s!"EXACT_DEPENDENCY_CLOSURE_END CONSTANTS {constants.size} THEOREMS {theoremCount}"
  /- Preserve native first-owner semantics for every indexed constant. Native
     IR-only names cannot be earlier than its first actual ConstantInfo. -/
  for i in [:irData.size] do
    for n in irData[i]!.extraConstNames do
      if let some owner := owners[n]? then
        unless owner.toNat ≤ i do
          throw <| IO.userError s!"Earlier IR ownership collision for {n}"
  let kernel : Kernel.Environment := { baseEnv.toKernelEnv with
    constants := SMap.fromHashMap constants false
    const2ModIdx := owners
  }
  let env := Environment.ofKernelEnv kernel
  let mut guarded := 0
  for (n, ci) in constants do
    let (original, owner) ← index.lookup n
    unless ptrEq original ci && owners[n]? == some owner do
      throw <| IO.userError s!"Retained ConstantInfo or ownership changed: {n}"
    if ci.isTheorem then
      if uncached.contains n then
        let .thmInfo thmVal := ci | throw <| IO.userError "Expected theorem info"
        unless (expressionNames thmVal.value).all constants.contains do
          throw <| IO.userError s!"Uncached theorem body is missing indexed dependencies: {n}"
      else
        let some _ := cache.find? env n |
          throw <| IO.userError s!"Missing original axiom-cache entry for theorem {n}"
        unless cache.find? env n == cachedAtOwner cache owner n do
          throw <| IO.userError s!"Original theorem cache-entry mismatch: {n}"
        guarded := guarded + 1
  unless guarded + uncached.size == theoremCount do
    throw <| IO.userError "Theorem axiom-cache coverage count mismatch"
  stamp s!"ORIGINAL_THEOREM_AXIOM_CACHE_GUARD {guarded} BODY_CLOSED {uncached.size} TOTAL {theoremCount}"
  stamp "EXACT_ORIGINAL_CONSTANTINFO_IDENTITY_AND_OWNERSHIP_ACCEPTED"
  if checkParity then
    stamp "STANDARD_IMPORT_PARITY_BEGIN"
    let standard ← finalizeImport imported imports opts (trustLevel := 0)
      (leakEnv := false) (loadExts := false) (level := .private) (isModule := false)
    for (n, ci) in constants do
      let some full := standard.toKernelEnv.find? n |
        throw <| IO.userError s!"Standard import lacks retained CI: {n}"
      unless ptrEq full ci && standard.toKernelEnv.const2ModIdx[n]? == owners[n]? do
        throw <| IO.userError s!"Standard import CI/owner parity failure: {n}"
    stamp s!"STANDARD_IMPORT_EXACT_CI_OWNER_PARITY_ACCEPTED {constants.size}"
  return env

end ExactKernelSubenvironment


namespace ExactImportUnionAudit
open ExactKernelSubenvironment

/-- This deliberately uses Lean's own merge relation. An empty lookup map makes
    its axiom/axiom predicate test conservative: those cases fail for review. -/
def merge (previous candidate : ConstantInfo) : IO ConstantInfo := do
  if Lean.subsumesInfo {} candidate previous then return candidate
  if Lean.subsumesInfo {} previous candidate then return previous
  throw <| IO.userError s!"Incompatible or unresolved full-union duplicate {candidate.name}"

def scan (index : Index) : IO Nat := do
  let mut cursor := 0
  let mut duplicates := 0
  let mut collisionGroups := 0
  while cursor < index.entries.size do
    let hashKey := index.entries[cursor]! / 4294967296
    let mut stop := cursor + 1
    while stop < index.entries.size && index.entries[stop]! / 4294967296 == hashKey do
      stop := stop + 1
    if stop > cursor + 1 then
      collisionGroups := collisionGroups + 1
      let mut winners : Array ConstantInfo := #[]
      for pos in [cursor:stop] do
        let (ci, _) ← index.at (index.entries[pos]! % 4294967296)
        let mut found := false
        for i in [:winners.size] do
          if winners[i]!.name == ci.name then
            winners := winners.set! i (← merge winners[i]! ci)
            duplicates := duplicates + 1
            found := true
            break
        if !found then winners := winners.push ci
    cursor := stop
  stamp s!"GLOBAL_DUPLICATE_COMPATIBILITY_ACCEPTED CONSTANTS {index.entries.size} EXACT_NAME_DUPLICATES {duplicates} HASH_COLLISION_GROUPS {collisionGroups}"
  return duplicates

def fixtureCI (name : Name) (type : Expr) : ConstantInfo := .axiomInfo {
  name, levelParams := [], type, isUnsafe := false }

def fixtures : IO Unit := do
  let a := fixtureCI `ExactImportUnionAudit.conflict (mkConst ``True)
  let b := fixtureCI `ExactImportUnionAudit.conflict (mkConst ``False)
  let negativePassed ← try
    let _ ← merge a b
    pure false
  catch _ => pure true
  unless negativePassed do
    throw <| IO.userError "Incompatible duplicate negative control was accepted"
  stamp "INCOMPATIBLE_DUPLICATE_NEGATIVE_CONTROL_REJECTED"
  let first := fixtureCI `ExactImportUnionAudit.first (mkConst ``True)
  let second := fixtureCI `ExactImportUnionAudit.second (mkConst ``False)
  let d : ModuleData := {
    isModule := false
    imports := #[]
    extraConstNames := #[]
    entries := #[]
    constNames := #[first.name, second.name]
    constants := #[first, second]
  }
  -- Force a hash collision in a synthetic index. Different full names must not
  -- be merged even when the narrowing hash is identical.
  let collision : Index := { modules := #[d], starts := #[0, 2], entries := #[0, 1] }
  unless (← scan collision) == 0 do
    throw <| IO.userError "Different full names were merged by hash alone"
  stamp "FULL_NAME_HASH_COLLISION_CONTROL_ACCEPTED"

def audit : IO Unit := do
  fixtures
  let imports : Array Import := #[{ module := `ForestCore.MathlibFloor38 }, { module := `ForestCore.MathlibFloor38Target }]
  stamp "GLOBAL_UNION_IMPORT_CORE_BEGIN"
  let (_, imported) ← importModulesCore imports (globalLevel := .private) |>.run
  stamp "GLOBAL_UNION_IMPORT_CORE_END"
  let modules := imported.moduleNames.filterMap (imported.moduleNameMap[·]?)
  let data ← modules.mapM fun mod => do
    let some d := mod.mainModule? | throw <| IO.userError "Missing original module data"
    return d
  let index ← buildIndex data
  let _ ← scan index
  stamp "FULL_ORIGINAL_IMPORT_UNION_COMPATIBILITY_ACCEPTED"

end ExactImportUnionAudit

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  ExactImportUnionAudit.audit
  return 0

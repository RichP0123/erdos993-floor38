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

namespace Floor38KernelAssembly

def checkedOptions : Options :=
  ({} : Options).setBool `debug.skipKernelTC false |>.set `maxHeartbeats (0 : Nat)

def nameFromString (s : String) : Name :=
  (s.splitOn ".").foldl Name.str .anonymous

def stamp (s : String) : IO Unit := do
  IO.println s!"{← IO.monoMsNow} {s}"
  (← IO.getStdout).flush

unsafe def loadProofEnvironment (imports : Array Import) (seeds freshNames : Array Name) : IO Environment :=
  ExactKernelSubenvironment.load imports seeds freshNames checkedOptions
    (checkParity := imports.size == 1)

/-- Initialize exactly the standard cached-axiom extension. This is the same
addImportedFn/setState pair used by finalizePersistentExtensions, without its
unrelated tactic and compiler metadata. The contents are not fabricated. -/
def initializeAxiomCache (env : Environment) : IO Environment := do
  let extensions ← persistentEnvExtensionsRef.get
  let candidates := extensions.filter fun ext =>
    (ext.name.toString.splitOn "exportedAxiomsExt").length > 1
  unless candidates.size == 1 do
    throw <| IO.userError s!"Expected exactly one standard axiom-cache extension; found {candidates.size}"
  let ext := candidates[0]!
  stamp s!"AXIOM_CACHE_BEGIN {ext.name}"
  let old := ext.toEnvExtension.getState (asyncMode := .sync) env
  let newState ← ext.addImportedFn old.importedEntries { env, opts := checkedOptions }
  let env := ext.toEnvExtension.setState (asyncMode := .sync) env { old with state := newState }
  stamp "AXIOM_CACHE_END"
  return env

def kernelAdd (env : Environment) (decl : Declaration) : IO Environment := do
  unless !debug.skipKernelTC.get checkedOptions do
    throw <| IO.userError "Kernel checking must be enabled"
  stamp s!"KERNEL_CHECK_BEGIN {decl.getNames}"
  match env.toKernelEnv.addDecl checkedOptions decl with
  | .error err =>
    throw <| IO.userError s!"Kernel rejected declaration: {← (err.toMessageData checkedOptions).toString}"
  | .ok checked =>
    stamp "KERNEL_CHECK_ACCEPTED"
    return Environment.ofKernelEnv checked

/-- The deliberately ill-typed declaration must be rejected, and is never added. -/
def negativeControl (env : Environment) : IO Unit := do
  let bad : Declaration := .thmDecl {
    name := `Floor38KernelAssembly.rejectedNegativeControl
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro
  }
  match env.toKernelEnv.addDecl checkedOptions bad with
  | .ok _ => throw <| IO.userError "FATAL: ill-typed negative control was accepted"
  | .error _ => stamp "NEGATIVE_CONTROL_REJECTED"

def checkedAxioms (env : Environment) (declName : Name) : IO Unit := do
  let axioms ← (collectAxioms declName : CoreM (Array Name)).toIO'
    { fileName := "FinalKernelAssembler.lean", fileMap := default,
      options := checkedOptions }
    { env }
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  unless axioms.all allowed.contains do
    throw <| IO.userError s!"Unexpected axiom dependencies: {axioms}"
  IO.println s!"'{declName}' depends on axioms: [{String.intercalate ", " (axioms.toList.map toString)}]"
  (← IO.getStdout).flush

def requiredConstant (env : Environment) (name : Name) : IO ConstantInfo :=
  match env.toKernelEnv.find? name with
  | some ci => pure ci
  | none => throw <| IO.userError s!"Missing imported declaration {name}"

def expectedFinalType (env : Environment) : IO Expr := do
  let info ← requiredConstant env `Erdos993.floor38ExpectedStatement
  let .defnInfo statement := info |
    throw <| IO.userError "Independent expected statement must be a proposition definition"
  return statement.value

/-- Syntactic binder instantiation. This performs no typechecking; the final
ordinary kernel check validates every argument and every definitional equality. -/
def applyArguments (ci : ConstantInfo) (args : Array Expr) : IO (Expr × Expr) := do
  unless ci.levelParams.isEmpty do
    throw <| IO.userError s!"Unexpected universe parameters on {ci.name}"
  let mut term := mkConst ci.name
  let mut ty := ci.type
  for arg in args do
    let .forallE _ _ body _ := ty |
      throw <| IO.userError s!"Too many arguments for {ci.name}"
    term := mkApp term arg
    ty := body.instantiate1 arg
  return (term, ty)

/-- Instantiate the common row function and the already checked equality premises
of a supplied_order theorem. Eq.refl does not assert its two endpoints equal:
Lean's kernel must confirm the original expected RHS by definitional reduction. -/
def instantiateOrder (env : Environment) (codes : Expr) (n : Nat) : IO Expr := do
  let ci ← requiredConstant env <| nameFromString s!"Erdos993.Floor216.supplied_order{n}"
  let (firstTerm, firstType) ← applyArguments ci #[codes]
  let mut term := firstTerm
  let mut ty := firstType
  let mut equalities := 0
  while true do
    let .forallE _ domain body _ := ty | break
    let .const eqName levels := domain.getAppFn | break
    if eqName != ``Eq then break
    let eqArgs := domain.getAppArgs
    unless eqArgs.size == 3 do
      throw <| IO.userError s!"Malformed equality premise in {ci.name}"
    let refl := mkAppN (mkConst ``Eq.refl levels) #[eqArgs[0]!, eqArgs[1]!]
    term := mkApp term refl
    ty := body.instantiate1 refl
    equalities := equalities + 1
  unless equalities > 0 do
    throw <| IO.userError s!"No row equality premises in {ci.name}"
  stamp s!"ORDER_TERM {n} ROW_EQUALITIES {equalities}"
  return term

def saveChecked (env : Environment) (output : System.FilePath) : IO Unit := do
  stamp "SERIALIZATION_BEGIN"
  writeModule (writeIR := false) env output
  stamp s!"SERIALIZATION_END {output}"


end Floor38KernelAssembly

namespace MathlibFloor38Kernel
open Floor38KernelAssembly

def finalName : Name := `Erdos993.ForestCore.mathlib_forest_unimodal_through_thirty_seven
def targetName : Name := `Erdos993.ForestCore.mathlibFloor38Target
def helperName : Name := `Erdos993.ForestCore.mathlibFloor38FromOriginal
def originalName : Name := `Erdos993.Floor216.actual_forest_unimodal_through_thirty_seven
def aliasName : Name := `Erdos993.ForestCore.mathlib_floor38_roundtrip_verified

def expected (env : Environment) : IO DefinitionVal := do
  let .defnInfo info ← requiredConstant env targetName |
    throw <| IO.userError "Mathlib target must be a definition, never an axiom"
  unless info.levelParams.length == 1 do
    throw <| IO.userError "Mathlib target must quantify over one arbitrary universe"
  return info

unsafe def assemble (outputModule : Name) (output : System.FilePath) : IO Unit := do
  let imports : Array Import := #[{ module := `Floor38FinalCandidate },
    { module := `ForestCore.MathlibFloor38Target }]
  let env ← loadProofEnvironment imports
    #[originalName, targetName, helperName, `Erdos993.floor38ExpectedStatement] #[finalName]
  let env := env.setMainModule outputModule
  let env ← initializeAxiomCache env
  negativeControl env
  let original ← requiredConstant env originalName
  unless original.isTheorem && original.levelParams.isEmpty do
    throw <| IO.userError "Original floor proof must be the monomorphic theorem"
  unless original.type == (← expectedFinalType env) do
    throw <| IO.userError "Original floor theorem has an unexpected or conditional signature"
  checkedAxioms env originalName
  let target ← expected env
  let helper ← requiredConstant env helperName
  unless helper.isTheorem && helper.levelParams.length == 1 do
    throw <| IO.userError "Transport specialization must be a universe-polymorphic theorem"
  let levels := target.levelParams.map Level.param
  let proof := mkApp (mkConst helperName levels) (mkConst originalName)
  let env ← kernelAdd env <| .thmDecl {
    name := finalName, levelParams := target.levelParams,
    type := target.value, value := proof }
  stamp "EXACT_UNCONDITIONAL_MATHLIB_FLOOR38_SIGNATURE_ACCEPTED"
  checkedAxioms env finalName
  saveChecked env output

unsafe def verify (outputModule : Name) (output : System.FilePath) : IO Unit := do
  let imports : Array Import := #[{ module := `ForestCore.MathlibFloor38 },
    { module := `ForestCore.MathlibFloor38Target }]
  let env ← loadProofEnvironment imports #[finalName, targetName] #[aliasName]
  let env := env.setMainModule outputModule
  let env ← initializeAxiomCache env
  negativeControl env
  let proof ← requiredConstant env finalName
  let target ← expected env
  unless proof.isTheorem do
    throw <| IO.userError "Reimported Mathlib result is not a theorem"
  unless proof.levelParams == target.levelParams && proof.type == target.value do
    throw <| IO.userError "Reimported Mathlib theorem has the wrong literal type/universes"
  stamp "REIMPORTED_THEOREM_KIND theorem"
  stamp "EXACT_UNCONDITIONAL_MATHLIB_FLOOR38_SIGNATURE_ACCEPTED"
  let env ← kernelAdd env <| .thmDecl {
    name := aliasName, levelParams := target.levelParams, type := target.value,
    value := mkConst finalName (target.levelParams.map Level.param) }
  checkedAxioms env finalName
  checkedAxioms env aliasName
  saveChecked env output

end MathlibFloor38Kernel

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | ["assemble", outputModule, output] =>
    MathlibFloor38Kernel.assemble (Floor38KernelAssembly.nameFromString outputModule) output
  | ["verify", outputModule, output] =>
    MathlibFloor38Kernel.verify (Floor38KernelAssembly.nameFromString outputModule) output
  | _ => throw <| IO.userError "Expected assemble|verify OUTPUT_MODULE OUTPUT_OLEAN"
  return 0

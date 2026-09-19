import CDotFCCT.CTML.CarrierEquationInterpretation
import CDotFCCT.CTML.MixedRecursion

/-!
# Coupled carrier and ordinary runtime equations

The inner finite carrier system is solved by recursion on record structure. Its
parameters may mention a finite vector of runtime rows, solved by the observation
index. Every runtime dependency, including an occurrence through a carrier name,
is guarded by an ordinary record or another existing mixed guard.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Mixed

open CTMLCore (WFTy)
open CTMLCore.Syntax CTMLCore.Indexed

/-- Guarding every name in a finite prefix permits simultaneous changes below the index. -/
theorem interpret_guarded_prefix (ghost : FieldName → Bool) {type : Ty} {size n : Nat}
    (guarded : ∀ index : Fin size, GuardedAt ghost index type) {left right : Environment}
    (before : ∀ index k, k < n → left index k = right index k)
    (outside : ∀ index, size ≤ index → Agree n (left index) (right index)) :
    interpret ghost left type n = interpret ghost right type n := by
  induction size generalizing left with
  | zero => exact interpret_congr ghost type (fun index => outside index (Nat.zero_le _))
  | succ size ih =>
      let middle : Environment := fun index => if index = size then right index else left index
      apply (interpret_guarded ghost (guarded ⟨size, Nat.lt_succ_self _⟩)
        (left := left) (right := middle) ?_).trans
      · apply ih (fun index => guarded ⟨index, Nat.lt_succ_of_lt index.isLt⟩)
        · intro index k smaller
          by_cases equal : index = size
          · simp only [middle, ite_eq_left equal]
          · simpa only [middle, ite_eq_right equal] using before index k smaller
        · intro index after k within
          by_cases equal : index = size
          · simp only [middle, ite_eq_left equal]
          · simpa only [middle, ite_eq_right equal] using outside index (by omega) k within
      · refine ⟨?_, ?_⟩
        · intro index different k within
          simp only [middle, ite_eq_right different]
        · intro k smaller
          simpa only [middle, ↓reduceIte] using before size k smaller

namespace CarrierRuntime

structure System (ghost : FieldName → Bool) (depth runtimeSize carrierSize : Nat) where
  carriers : CarrierEquation.System ghost (depth + runtimeSize) carrierSize
  body : Fin runtimeSize → WFTy ((depth + runtimeSize) + carrierSize)
  guarded : ∀ component (index : Fin (runtimeSize + carrierSize)),
    GuardedAt ghost index (body component).raw

variable {ghost : FieldName → Bool} {depth runtimeSize carrierSize : Nat}

/-- Carrier parameters see all runtime names, before the carrier block is introduced. -/
def System.carrierValues (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) (runtime : Fin runtimeSize → Candidate) : Fin carrierSize → Candidate :=
  system.carriers.interpretation (env.prepend runtime)

def System.extend (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) (runtime : Fin runtimeSize → Candidate) : Environment :=
  (env.prepend runtime).prepend (system.carrierValues env runtime)

def System.operator (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) (runtime : Nat → Fin runtimeSize → Observation) (n : Nat) :
    Fin runtimeSize → Observation :=
  fun index => interpret ghost (system.extend env (fun index k => runtime k index))
    (system.body index).raw n

/-- Solving the inner pure block preserves agreement strictly below the observation index. -/
theorem System.extend_before (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) {left right : Nat → Fin runtimeSize → Observation} {n : Nat}
    (agree : ∀ k, k < n → left k = right k) (index k : Nat) (smaller : k < n) :
    system.extend env (fun index k => left k index) index k =
      system.extend env (fun index k => right k index) index k := by
  by_cases carrier : index < carrierSize
  · have equal := system.carriers.solution_congr
      (fun type => interpret_congr ghost type.raw (env.prepend_before agree smaller))
      ⟨index, carrier⟩
    simpa only [System.extend, Environment.prepend, dite_eq_left carrier,
      System.carrierValues, CarrierEquation.System.interpretation] using equal
  · simpa only [System.extend, Environment.prepend, dite_eq_right carrier] using
      env.prepend_before agree smaller (index - carrierSize) k (Nat.le_refl _)

/-- Ordinary guards make the entire coupled runtime operator contractive. -/
theorem System.contractive (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) : Contractive (system.operator env) := by
  intro n left right agree
  funext component
  apply interpret_guarded_prefix ghost (system.guarded component)
  · exact system.extend_before env agree
  · intro index outside k within
    have carrier : ¬index < carrierSize := by omega
    have runtime : ¬index - carrierSize < runtimeSize := by omega
    simp only [System.extend, Environment.prepend, dite_eq_right carrier, dite_eq_right runtime]

def System.runtimeSolution (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) : Nat → Fin runtimeSize → Observation :=
  fixedPoint (system.operator env) (fun _ => (fun _ => False, fun _ => False))

def System.runtimeValues (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) (index : Fin runtimeSize) : Candidate :=
  fun n => system.runtimeSolution env n index

def System.carrierInterpretation (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) : Fin carrierSize → Candidate :=
  system.carrierValues env (system.runtimeValues env)

def System.environment (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) : Environment := system.extend env (system.runtimeValues env)

theorem System.runtime_unfold (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) (index : Fin runtimeSize) (n : Nat) :
    system.runtimeValues env index n =
      interpret ghost (system.environment env) (system.body index).raw n :=
  congrFun (fixedPoint_unfold (system.contractive env) _ n) index

theorem System.runtime_downward (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) (index : Fin runtimeSize) : Downward (system.runtimeValues env index) := by
  intro m n within term
  rw [system.runtime_unfold env index n, system.runtime_unfold env index m]
  exact interpret_downward ghost (system.body index).raw _ m n within term

theorem System.carrier_downward (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) (index : Fin carrierSize) :
    Downward (system.carrierInterpretation env index) :=
  system.carriers.downward (env.prepend (system.runtimeValues env)) index

/-- Runtime names follow the entire carrier block in the combined environment. -/
def System.runtimeName (_ : System ghost depth runtimeSize carrierSize)
    (index : Fin runtimeSize) : WFTy ((depth + runtimeSize) + carrierSize) :=
  WFTy.var (carrierSize + index) (by omega)

theorem System.runtime_name (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) (index : Fin runtimeSize) :
    interpret ghost (system.environment env) (system.runtimeName index).raw =
      system.runtimeValues env index := by
  change prefixClosure (system.environment env (carrierSize + index)) = _
  have outside : ¬carrierSize + index.val < carrierSize := by omega
  simp only [System.environment, System.extend, Environment.prepend, dite_eq_right outside,
    Nat.add_sub_cancel_left, dite_eq_left index.isLt]
  exact prefixClosure_eq (system.runtime_downward env index)

/-- Every runtime equation is solved in the same environment as the carrier equations. -/
theorem System.runtime_equation (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) (index : Fin runtimeSize) :
    interpret ghost (system.environment env) (system.runtimeName index).raw =
      interpret ghost (system.environment env) (system.body index).raw :=
  (system.runtime_name env index).trans (funext (system.runtime_unfold env index))

theorem System.carrier_name (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) (index : Fin carrierSize) :
    interpret ghost (system.environment env) (system.carriers.name index).raw =
      system.carrierInterpretation env index :=
  system.carriers.interpret_name (env.prepend (system.runtimeValues env))
    (system.carrierInterpretation env) (system.carrier_downward env) index

/-- Pure carrier cycles remain exact when their runtime parameters close a guarded feedback loop. -/
theorem System.carrier_equation (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) (index : Fin carrierSize) :
    interpret ghost (system.environment env) (system.carriers.name index).raw =
      interpret ghost (system.environment env) (system.carriers.compile index).raw :=
  system.carriers.equation (env.prepend (system.runtimeValues env)) index

/-- The combined block is ordered carrier names, runtime names, then outer names. -/
def System.size (_ : System ghost depth runtimeSize carrierSize) : Nat :=
  runtimeSize + carrierSize

def System.values (system : System ghost depth runtimeSize carrierSize) (env : Environment)
    (index : Fin system.size) : Candidate :=
  if carrier : index.val < carrierSize then system.carrierInterpretation env ⟨index, carrier⟩
  else system.runtimeValues env ⟨index - carrierSize, by
    have within := index.isLt
    simp only [System.size] at within
    omega⟩

theorem System.values_downward (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) (index : Fin system.size) : Downward (system.values env index) := by
  unfold values
  split
  · exact system.carrier_downward env _
  · exact system.runtime_downward env _

theorem System.environment_eq_prepend (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) : system.environment env = env.prepend (system.values env) := by
  funext index
  by_cases carrier : index < carrierSize
  · have within : index < system.size := by simp only [System.size]; omega
    simp only [System.environment, System.extend, Environment.prepend, dite_eq_left carrier,
      dite_eq_left within, System.values, System.carrierInterpretation]
  · by_cases runtime : index - carrierSize < runtimeSize
    · have within : index < system.size := by simp only [System.size]; omega
      simp only [System.environment, System.extend, Environment.prepend, dite_eq_right carrier,
        dite_eq_left runtime, dite_eq_left within, System.values]
    · have outside : ¬index < system.size := by simp only [System.size]; omega
      simp only [System.environment, System.extend, Environment.prepend, dite_eq_right carrier,
        dite_eq_right runtime, dite_eq_right outside]
      exact congrArg env (by simp only [System.size, Nat.sub_sub, Nat.add_comm])

theorem System.environment_lifted (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) : Environment.Lifted 0 system.size env (system.environment env) :=
  system.environment_eq_prepend env ▸ env.prepend_lifted (system.values env)

def System.name (system : System ghost depth runtimeSize carrierSize)
    (index : Fin system.size) : WFTy (depth + system.size) :=
  WFTy.var index (Nat.lt_of_lt_of_le index.isLt (Nat.le_add_left _ _))

def System.bodyAt (system : System ghost depth runtimeSize carrierSize)
    (index : Fin system.size) : WFTy (depth + system.size) :=
  if carrier : index.val < carrierSize then
    (system.carriers.compile ⟨index, carrier⟩).castDepth (by simp only [System.size]; omega)
  else
    (system.body ⟨index - carrierSize, by
      have within := index.isLt
      simp only [System.size] at within
      omega⟩).castDepth (by simp only [System.size]; omega)

theorem System.interpret_name (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) (index : Fin system.size) :
    interpret ghost (system.environment env) (system.name index).raw =
      system.values env index := by
  change prefixClosure (system.environment env index) = _
  rw [system.environment_eq_prepend env]
  simp only [Environment.prepend, dite_eq_left index.isLt]
  exact prefixClosure_eq (system.values_downward env index)

/-- Both blocks satisfy exact equations in a single scope with the total block depth. -/
theorem System.equation (system : System ghost depth runtimeSize carrierSize)
    (env : Environment) (index : Fin system.size) :
    interpret ghost (system.environment env) (system.name index).raw =
      interpret ghost (system.environment env) (system.bodyAt index).raw := by
  rw [system.interpret_name env index]
  by_cases carrier : index.val < carrierSize
  · simpa only [System.values, System.bodyAt, dite_eq_left carrier, WFTy.raw_castDepth] using
      (system.carrier_name env ⟨index, carrier⟩).symm.trans
        (system.carrier_equation env ⟨index, carrier⟩)
  · simpa only [System.values, System.bodyAt, dite_eq_right carrier, WFTy.raw_castDepth] using
      funext (system.runtime_unfold env ⟨index - carrierSize, by
        have within := index.isLt
        simp only [System.size] at within
        omega⟩)

end CarrierRuntime

end CDotFCCT.CTML.Mixed

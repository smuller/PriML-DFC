signature PRIMLSOLVER =
sig
    type solver
    val setup : string option -> Context.context -> Variable.var list -> solver
    val add_constraint : solver * (IL.prio * IL.prio) -> solver
    val add_negated_constraint : solver * (IL.prio * IL.prio) -> solver
    val add_negate_and_constraints : solver * (IL.prio * IL.prio) list -> solver
    val check : solver -> bool
    val add_comment : solver * string -> solver

    val solvercalls : int ref
    val solvertime : LargeInt.int ref
end

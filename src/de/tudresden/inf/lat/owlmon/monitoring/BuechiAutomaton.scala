package de.tudresden.inf.lat.owlmon.monitoring

import scala.collection.mutable.Map
import scala.collection.mutable.Set
import scala.collection.mutable.Stack

/** This class represents a Buechi automaton.
  *
  * @author Marcel Lippmann
  */
class BuechiAutomaton {

  val initialStates = Set[String]()

  val finalStates = Set[String]()

  // transitions: State -> Symbol -> 2^State.
  private val trans = Map[String, Map[Set[String], Set[String]]]()

  /** This method returns the set of transitions.
    *
    * @return The set of transitions.
    */
  def transitions = trans

  /** This method is used to add another transition to the Buechi automaton.
    *
    * @param sourceState
    *   The source state of the transition.
    * @param symbol
    *   The symbol, i.e. set of propositional variables that are true, to be
    *   read in the transition.
    * @param destState
    *   The destination state of the transition.
    */
  def addTransition(sourceState: String,
                    symbol: Set[String],
                    destState: String): Unit = {

    trans.get(sourceState) match {

      case Some(t) => {
        t.get(symbol) match {
          case Some(dests) => dests += destState
          case None => t += symbol -> Set(destState)
        }
      }

      case None => trans += sourceState -> Map(symbol -> Set(destState))
    }
  }

  /** This field is used for Tarjan's algorithm for detecting all strongly
    * connected components.
    *
    * It is a counter for the visit numbers.
    */
  private var index = 0

  /** This field is used for Tarjan's algorithm for detecting all strongly
    * connected components.
    *
    * It is the DFS stack.
    */
  private val stack = Stack[String]()
	
  /** This field is used for Tarjan's algorithm for detecting all strongly
    * connected components.
    *
    * It assigns to each state an index.
    */
  private val ind = Map[String, Int]()

  /** This field is used for Tarjan's algorithm for detecting all strongly
    * connected components.
    *
    * It assigns to each state a lowlink.
    */
  private val ll = Map[String, Int]()

  /** This field is used for Tarjan's algorithm for detecting all strongly
    * connected components.
    *
    * It is the set of all found SCCs.
    */
  private val sccs = Set[Set[String]]()

  /** This method is used for Tarjan's algorithm for detecting all strongly
    * connected components.
    *
    * It is the `visit` function of the algorithm.
    *
    * @param state
    *   A state to visit.
    */
  private def visit(state: String): Unit = {

    // Set state index and lowlink to visit number.
    ind += state -> index
    ll += state -> index

    index += 1

    // Push state on DFS stack.
    stack.push(state)

    // For all successors of the state:
    for (t <- trans.get(state); s <- t.values.flatten) {

      // Was 's' visited?
      if (!ind.get(s).isDefined) {

        visit(s)

        // Propagate lowlink if less.
        ll += state -> ll.get(state).get.min(ll.get(s).get)

      } else if (stack.contains(s)) {

        ll += state -> ll.get(state).get.min(ind.get(s).get)
      }
    }

    // Is state a DFS root?
    if (ll.get(state) == ind.get(state)) {

      // Pop states off DFS stack down to 'state'.
      val scc = Set[String]()
      while (stack.top != state) {
        scc += stack.pop
      }
      scc += stack.pop
      sccs += scc
    }
  }

  /** This method implements Tarjan's algorithm for detecting all stronly
    * connected components.
    */
  private def computeSCCs(): Unit = {

    // Introduce dummy initial state.
    val init = "dummy_initial"
    trans += init -> Map(Set("<SIGMA>") -> initialStates)

    // Initialise index, DFS stack, state indeces and lowlinks, and the set
    // of SCCs.
    index = 0
    stack.clear()
    ind.clear()
    ll.clear()
    sccs.clear()

    // Call visit function for dummy initial state.
    visit(init)

    // Remove dummy initial state.
    sccs.remove(Set(init))
    trans.remove(init)

    // Clean up data structures.
    stack.clear()
    ind.clear()
    ll.clear()
  }

  /** This method is used by the optimisation method.
    *
    * It checks whether a state has a self-loop.
    *
    * @param state
    *   The state to check.
    * @return `true` iff `state` has a self-loop.
    */
  private def hasSelfLoop(state: String): Boolean = {

    trans.get(state) exists (_.values exists (_.contains(state)))
  }

  /** This method is used to optimise the automaton.
    *
    * States that cannot be part of an accepting run are removed.
    */
  def optimise(): Unit = {

    // Compute the set of good states, i.e. states that can be part of an
    // accepting run. Such states are reachable and can reach a non-trivial SCC
    // that contains a final state.

    // (1) Compute all reachable SCCs and store them in the field 'sccs'.
    computeSCCs()

    // (2) Remove all SCCs that cannot reach a final state.
    val badStates = Set[String]()
    var changed = true
    while (changed) {

      changed = false

      sccs foreach { scc => {
        
          // All SCCs that do not have a final state or consist only of a final
          // state that does not have a self-loop need to be checked.
          if (scc.intersect(finalStates).isEmpty ||
              (scc.size == 1 && !hasSelfLoop(scc.head))) {

            // Check whether state that does not belong to the current SCC can be
            // reached.
            var continueSearch = true
            for (s <- scc; t <- trans.get(s); succ <- t.values; if continueSearch) {
              
              succ --= badStates
              
              // Check for successors that are not already removed and do not
              // belong to the current SCC.
              if (!succ.isEmpty && succ.intersect(scc).isEmpty) {

                // Stop searching iff good SCC found.
                continueSearch = false

              }
            }

            // If current SCC is bad:
            if (continueSearch) {
              badStates ++= scc
              sccs -= scc
              changed = true
            }

          }
        }
      }
    }

    // (3) The remaining SCCs are good SCCs. Remove all other states.
    val goodStates = sccs.flatten

    // SCCs are no longer needed.
    sccs.clear()

    // Clean initial states.
    initialStates.retain(goodStates.contains(_))

    // Clean final states.
    finalStates.retain(goodStates.contains(_))

    // Clean transitions.
    for (s <- trans.keys) {

      if (!goodStates.contains(s)) {

        // Remove transitions with bad lhs.
        trans -= s

      } else {

        // Remove transitions with bad rhs.
        val t = trans.get(s).getOrElse(Map())
        for (sym <- t.keys) {

          val st = t.get(sym).getOrElse(Set())
          st.retain(goodStates.contains(_))

          if (st.isEmpty) {
            t -= sym
          } else {
            t += sym -> st
          }
        }
      }
    }
  }

  override def toString: String = {

    val strBuilder = new StringBuilder("Initial States:\n  ")
    strBuilder append initialStates.mkString("\n  ")
    strBuilder append "\n\nFinal States:\n  "

    strBuilder append finalStates.mkString("\n  ")

    strBuilder append "\n\nTransitions:\n"
    for (state <- trans.keys; t <- trans.get(state); symbol <- t.keys) {
      strBuilder append "  "
      strBuilder append state
      strBuilder append " --"
      strBuilder append symbol
      strBuilder append "--> "
      strBuilder append t.get(symbol).get
      strBuilder append "\n"
    }

    strBuilder.toString
  }
}

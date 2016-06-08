package de.tudresden.inf.lat.owlmon.util

import scala.collection.JavaConversions._

import scala.collection.mutable.Map
import scala.collection.mutable.Set

import org.semanticweb.owlapi.model.IRI
import org.semanticweb.owlapi.model.OWLAxiom
import org.semanticweb.owlapi.model.OWLOntology
import org.semanticweb.owlapi.model.OWLOntologyCreationException
import org.semanticweb.owlapi.model.OWLOntologyManager

import rwth.i2.ltl2ba4j.LTL2BA4J

import de.tudresden.inf.lat.owlmon.datastructures.ALCLTLFormula

import de.tudresden.inf.lat.owlmon.monitoring.BuechiAutomaton

/** This object contains helper methods for operating with Buechi automata.
  *
  * @author Marcel Lippmann
  */
object BuechiTools {

  /** This method is used to determine the set of successor states for a given
    * state and a given input in a given Buechi automaton.
    *
    * A transition can be made iff the input ontology is consistent with the
    * symbol of the transition.
    *
    * @param ba
    *   The Buechi automaton.
    * @param state
    *   The state to start with.
    * @param input
    *   The input to be read.
    * @param manager
    *   The ontology manager.
    * @param translationMap
    *   The map that translates variables to axioms.
    * @return The set of successor states.
    */
  def computeSuccessorStates(ba: BuechiAutomaton,
                             state: String,
                             input: OWLOntology,
                             manager: OWLOntologyManager,
                             translationMap: Map[String, OWLAxiom]): Set[String] = {

    val succ = Set[String]()

    val trans = ba.transitions.get(state).getOrElse(Map())
      
    trans.keys foreach { sym => {
            
        // Translate symbol to set of axioms.
        val axs = (sym map (translationMap.get(_).get)).toSet

        // If the set of axioms together with the input is consistent, add
        // successor states.
        if (OntologyTools.isConsistent(manager, axs union input.getAxioms)) {
          succ ++= trans.get(sym).get
        }
      }
    }

    succ
  }

  /** This method is used to determine the set of successor states for a given
    * set of states and a given input in a given Buechi automaton.
    *
    * A transition can be made iff the input ontology is consistent with the
    * symbol of the transition.
    *
    * @param ba
    *   The Buechi automaton.
    * @param states
    *   The set of states to start.
    * @param input
    *   The input to read.
    * @param manager
    *   The ontology manager.
    * @param translationMap
    *   The map translation variables to axioms.
    * @return The set of successor states.
    */
  def computeSuccessorStates(ba: BuechiAutomaton,
                             states: Set[String],
                             input: OWLOntology,
                             manager: OWLOntologyManager,
                             translationMap: Map[String, OWLAxiom]): Set[String] = {

    states flatMap (computeSuccessorStates(ba, _, input, manager, translationMap))
  }

  /** This method is used to generate a Buechi automaton from an ALC-LTL
    * formula.
    *
    * @param formula
    *   The ALC-LTL formula that the Buechi automaton should be generated for.
    * @param globalOntology
    *   An (optional) global ontology that has to hold at each point in time.
    * @return The Buechi automaton for the ALC-LTL formula.
    */
  def generateBuechiAutomaton(formula: ALCLTLFormula,
                              globalOntology: Option[OWLOntology]): BuechiAutomaton = {

    val rigidNames = !formula.rigidIRIs.isEmpty

    val ba =
      generateBAUsingLTL2BA4J(formula, globalOntology, rigidNames) // LTL2BA4J uses the JNI bridge.
      //generateBAUsingLTL2Buchi(formula, globalOntology, rigidNames) // LTL2Buchi of JPF.

    if (rigidNames) {
      generateBARespRigidNames(ba, formula, globalOntology)
    } else {
      ba
    }
  }

  private def generateBARespRigidNames(ba: BuechiAutomaton,
                                       formula: ALCLTLFormula,
                                       globalOntology: Option[OWLOntology]): BuechiAutomaton = {

    val baRigid = new BuechiAutomaton

    // Compute the set of initial states, final states and transitions.

    val symbolsMap = Map(Set[Set[String]]() -> 0)
    var currentSymbolsNumber = 0

    def hash(symbols: Set[Set[String]]): Int = {
      symbolsMap.get(symbols).getOrElse {
        currentSymbolsNumber += 1
        symbolsMap += symbols -> currentSymbolsNumber
        currentSymbolsNumber
      }
    }

    def traverse(state: String, readSymbols: Set[Set[String]]) {

      val src = state + "-" + hash(readSymbols)

      // Check if not already traversed.
      if (!baRigid.transitions.get(src).isDefined) {

        // Check whether state is final.
        if (ba.finalStates.contains(state)) {
          baRigid.finalStates += src
        }

        // Add out-going transitions.
        val toTraverse = Set[(String, Set[Set[String]])]()
        for (t <- ba.transitions.get(state);
             sym <- t.keys) {

          // Check whether readSymbols together with sym is consistent.
          val symSet = readSymbols + sym
          val axSet = symSet map (ss => (ss map (formula.translationMap.get(_).get)).toSet)

          if (OntologyTools.isSetConsistent(formula.ontologyManager,
                                            axSet.toSet,
                                            formula.rigidIRIs.toSet)) {

            for (succ <- t.get(sym).get) {
              val dest = succ + "-" + hash(symSet)
              baRigid.addTransition(src, sym, dest)
              toTraverse += ((succ, symSet))
            }
          }
        }

        // Traverse destination states.
        toTraverse foreach (st => traverse(st._1, st._2))
      }
    }

    ba.initialStates foreach { s => {

        // The set of initial states is the same. We only rename the states.
        baRigid.initialStates += s + "-" + hash(Set())
        
        // Traverse the initial states.
        traverse(s, Set())
      }
    }

    baRigid
  }

  private def generateBAUsingLTL2BA4J(formula: ALCLTLFormula,
                                      globalOntology: Option[OWLOntology],
                                      complete: Boolean): BuechiAutomaton = {

    // Build automaton for propositional abstraction of formula.
    val transitions = LTL2BA4J.formulaToBA(formula.propAbs)

    // Translate to Buechi automaton representation.
    val ba = new BuechiAutomaton

    val ontMngr = formula.ontologyManager
    val transMap = formula.translationMap

    for (t <- transitions) {

      val src = t.getSourceState
      val dest = t.getTargetState
      val labels = t.getLabels

      // Translate labels.
      val symbol = labels map (_.getFullLabel)

      // Check symbol for consistency.
      val axioms = symbol map (transMap.get(_).get)

      val allAxioms = globalOntology match {
        case None => axioms
        case Some(go) => axioms union go.getAxioms
      }

      if (OntologyTools.isConsistent(ontMngr, allAxioms.toSet)) {

        // Add transition to Buechi automaton.
        if (complete) {

          for (sy <- computeAllTransitions(symbol, Set() ++ transMap.keys)) {

            // If 'sy' is consistent, add the transition.
            val newAxioms = sy map (transMap.get(_).get)
            val allAx = allAxioms union newAxioms
            if (OntologyTools.isConsistent(ontMngr, allAx.toSet)) {
              ba.addTransition(src.getLabel, sy, dest.getLabel)
            }
          }

        } else {

          ba.addTransition(src.getLabel, symbol, dest.getLabel)
        }

        // Add states to automaton.
        if (src.isInitial) {
          ba.initialStates += src.getLabel
        }

        if (src.isFinal) {
          ba.finalStates += src.getLabel
        }

        if (dest.isInitial) {
          ba.initialStates += dest.getLabel
        }

        if (dest.isFinal) {
          ba.finalStates += dest.getLabel
        }
      }
    }

    ba
  }

  private def computeAllTransitions(symbols: Set[String],
                                    alphabet: Set[String]): Set[Set[String]] = {

    // Helping function for computing all permutations of symbols and negated
    // symbols.
    def computeAllPermutations(ss: Set[String]): Set[Set[String]] = {
      if (ss.isEmpty) {
        Set(Set())
      } else {
        val s = ss.head
        val perm = computeAllPermutations(ss.tail)
        val pos = perm map (_ + s)
        val neg = perm map (_ + ("!" + s))
        pos ++ neg
      }
    }

    // Compute the set of variables a transition does not talk about.
    val newSym = (alphabet - "<SIGMA>") filter (!_.startsWith("!"))
    for (s <- symbols) {
      newSym -= (if (s.startsWith("!")) s.substring(1) else s)
    }

    // Compute of all permutations of those variables the new transitions.
    computeAllPermutations(newSym) map (_ ++ (symbols - "<SIGMA>"))
  }
}

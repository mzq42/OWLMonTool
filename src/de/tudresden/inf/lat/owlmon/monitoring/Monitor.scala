package de.tudresden.inf.lat.owlmon.monitoring

import org.semanticweb.owlapi.model.OWLOntology

import de.tudresden.inf.lat.owlmon.datastructures.ALCLTLFormula

import de.tudresden.inf.lat.owlmon.util.BuechiTools

/** This class describes a monitor for an ALC-LTL formula.
  *
  * It is built from an ALC-LTL formula and an (optional) global ontology and
  * an (optional) contraint formula.
  *
  * @author Marcel Lippmann
  */
class Monitor private (formula: ALCLTLFormula,
                       globalOntology: Option[OWLOntology],
                       constraints: Option[ALCLTLFormula]) {

  /** This constructor creates a monitor from an ALC-LTL formula without a
    * global ontology and a constraint formula.
    *
    * @param formula
    *  The ALC-LTL formula.
    */
  def this(formula: ALCLTLFormula) = {
    this(formula, None, None)
  }

  /** This constructor creates a monitor from an ALC-LTL formula with a global
    * ontology but without a contraint formula.
    *
    * @param formula
    *   The ALC-LTL formula.
    * @param globalOntology
    *   The global ontology that holds at each point in time.
    */
  def this(formula: ALCLTLFormula,
           globalOntology: OWLOntology) = {
    this(formula, Some(globalOntology), None)
  }

  /** This constructor creates a monitor from an ALC-LTL formula with a
    * contraint formula but without a global ontology.
    *
    * @param formula
    *   The ALC-LTL formula.
    * @param constraints
    *   An ALC-LTL formula that describes constraints that hold.
    */
  def this(formula: ALCLTLFormula,
           constraints: ALCLTLFormula) = {
    this(formula, None, Some(constraints))
  }

  /** This constructor creates a monitor from an ALC-LTL formula with a global
    * ontology and a contraint formula.
    *
    * @param formula
    *   The ALC-LTL formula.
    * @param globalOntology
    *   The global ontology that holds at each point in time.
    * @param constraints
    *   An ALC-LTL formula that describes constraints that hold.
    */
  def this(formula: ALCLTLFormula,
           globalOntology: OWLOntology,
           constraints: ALCLTLFormula) = {
    this(formula, Some(globalOntology), Some(constraints))
  }

  private var start: Long = _

  private def startProfiling() {
    start = System.currentTimeMillis
  }

  private def printProfiling(msg: String) {
    val end = System.currentTimeMillis
    val diff = end - start
    println(msg + " in: " +
      "%d min, %d.%d sec".format(
        (diff / 1000) / 60, (diff / 1000) % 60, diff % 1000))
  }

  startProfiling()
  private val ba = constraints match {
    case None => BuechiTools.generateBuechiAutomaton(
                   formula, globalOntology)
    case Some(c) => BuechiTools.generateBuechiAutomaton(
                      formula.getConjunction(c), globalOntology) 
  }
  printProfiling("BA")

  startProfiling()
  ba.optimise()
  printProfiling("BA optimised")

  startProfiling()
  private val baNot = constraints match {
    case None => BuechiTools.generateBuechiAutomaton(
                   formula.getNegation, globalOntology)
    case Some(c) => BuechiTools.generateBuechiAutomaton(
                      formula.getNegation.getConjunction(c), globalOntology)
  }
  printProfiling("BA-not")
  
  startProfiling()
  baNot.optimise()
  printProfiling("BA-not optimised")

  private var state = (ba.initialStates, baNot.initialStates)

  // @TODO: remove
  //println(ba)
  //println(baNot)

  /** This method returns the current state of the monitor.
    *
    * @return The current state.
    */
  def currentState = state

  /** This method is used to get the state output of the current state of the
    * monitor.
    *
    * @return The output of the monitor in the current state.
    */
  def getCurrentStateOutput: Output.OutputType = {

    // Calculate monitoring function.

    import Output._

    // If there is no accepting run on BA left:
    if (state._1.isEmpty) {
      Bottom

    // Else if there is no accepting run on BA-not left:
    } else if (state._2.isEmpty) {
      Top

    // Otherwise, if both is possible.
    } else {
      Unknown
    }
  }

  /** This method is used to make a step in the monitor.
    *
    * @param ontology
    *   The input to be read.
    */
  def makeStep(ontology: OWLOntology) {

    val succ = BuechiTools.computeSuccessorStates(
      ba, state._1, ontology, formula.ontologyManager, formula.translationMap)
    val succNot = BuechiTools.computeSuccessorStates(
      baNot, state._2, ontology, formula.ontologyManager, formula.translationMap)

    state = (succ, succNot)
  }
  
  /** This enumeration describes the monitor output.
    */
  object Output extends Enumeration {

    /** The output type variable.
      */
    type OutputType = Value

    /** Output 'top'.
      */
    val Top = Value

    /** Output 'bottom'.
      */
    val Bottom = Value
    
    /** Output 'unknown'.
      */
    val Unknown = Value
  }
}

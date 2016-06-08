package de.tudresden.inf.lat.owlmon.datastructures

import scala.collection.mutable.Map
import scala.collection.mutable.Set

import org.semanticweb.owlapi.model.IRI
import org.semanticweb.owlapi.model.OWLAxiom
import org.semanticweb.owlapi.model.OWLOntologyManager

/** This class describes an ALC-LTL formula.
  *
  * @constructor This constructor creates a new ALC-LTL formula from the given
  *   parameters.
  * @param propAbs
  *   The propositional abstraction of the formula.
  * @param ontologyManager
  *   The ontology manager.
  * @param translationMap
  *   A map translating propositional variables to axioms.
  * @param rigidIRIs
  *   A set of IRIs that are designated to be rigid.
  *
  * @author Marcel Lippmann
  */
class ALCLTLFormula(val propAbs: String,
                    val ontologyManager: OWLOntologyManager,
                    val translationMap: Map[String, OWLAxiom],
                    val rigidIRIs: Set[IRI]) {

  /** This constructor calls the standard constructor with the set of rigid
    * IRIs being empty.
    *
    * @param propAbs
    *   The propositional abstraction of the formula.
    * @param ontologyManager
    *   The ontology manager.
    * @param translationMap
    *   A map translating propositional variables to axioms.
    */
  def this(propAbs: String,
           ontologyManager: OWLOntologyManager,
           translationMap: Map[String, OWLAxiom]) = {

    this(propAbs, ontologyManager, translationMap, Set())
  }

  /** This method returns an ALC-LTL formula that is the negation
    * of this formala.
    *
    * @return The negation of this formula.
    */
  def getNegation: ALCLTLFormula = {
    new ALCLTLFormula("!(" + propAbs + ")", ontologyManager, translationMap, rigidIRIs)
  }

  /** This method returns an ALC-LTL formula that is the conjunction of this
    * formula and the formula given as argument.
    *
    * Note that the ontology manager of the returned formula will be the same
    * as of this formula. Also the translation map of the returned formula is
    * `t ++ t'` where `t` is the translation map of this formula and `t'` is
    * the translation map of the provided formula. The same is true for the set
    * of rigid IRIs.
    *
    * @param formula
    *   An ALC-LTL formula.
    */
  def getConjunction(formula: ALCLTLFormula) = {

    val mergedTransMap = translationMap ++ formula.translationMap
    val mergedRigidIRIs = rigidIRIs ++ formula.rigidIRIs
    new ALCLTLFormula("(" + propAbs + ") && (" + formula.propAbs + ")",
      ontologyManager, mergedTransMap, mergedRigidIRIs)
  }
}

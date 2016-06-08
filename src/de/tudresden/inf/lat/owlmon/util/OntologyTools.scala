package de.tudresden.inf.lat.owlmon.util

import scala.collection.JavaConversions._

import org.semanticweb.HermiT.Reasoner.ReasonerFactory

import org.semanticweb.owlapi.model.IRI
import org.semanticweb.owlapi.model.OWLAxiom
import org.semanticweb.owlapi.model.OWLClass
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom
import org.semanticweb.owlapi.model.OWLClassExpression
import org.semanticweb.owlapi.model.OWLNegativeObjectPropertyAssertionAxiom
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom
import org.semanticweb.owlapi.model.OWLObjectComplementOf
import org.semanticweb.owlapi.model.OWLObjectInverseOf
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf
import org.semanticweb.owlapi.model.OWLObjectProperty
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom
import org.semanticweb.owlapi.model.OWLObjectUnionOf
import org.semanticweb.owlapi.model.OWLOntology
import org.semanticweb.owlapi.model.OWLOntologyCreationException
import org.semanticweb.owlapi.model.OWLOntologyManager
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom

import org.semanticweb.owlapi.reasoner.ConsoleProgressMonitor
import org.semanticweb.owlapi.reasoner.OWLReasoner
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory
import org.semanticweb.owlapi.reasoner.SimpleConfiguration

/** This object contains useful helper functions to deal with OWL ontologies.
  *
  * @author Marcel Lippmann
  */
object OntologyTools {

  private val reasonerFactory: OWLReasonerFactory =
    new ReasonerFactory // HermiT

  /** This method returns `true` iff the given ontology is consistent.
    *
    * @param ontology
    *   The ontology to be checked for consistency.
    * @return `true` iff `ontology` is consistent.
    */
  def isConsistent(ontology: OWLOntology): Boolean = {

    val reasoner: OWLReasoner = reasonerFactory.createReasoner(ontology)

    val isCons = reasoner.isConsistent

    // Free memory of reasoner.
    reasoner.dispose

    isCons
  }

  /** This method returns `true` iff the given set of axioms is consistent.
    *
    * The ontology manager is used to create an ontology consisting of the
    * provided axioms and then a reasoner is used to check for consistency.
    *
    * @param ontologyManager
    *   The OWL ontology manager.
    * @param axioms
    *   The set of axioms to be checked for consistency.
    * @return `true` iff the set of axioms is consistent.
    */
  def isConsistent(ontologyManager: OWLOntologyManager,
                   axioms: Set[OWLAxiom]): Boolean = {

    val ontology: OWLOntology = ontologyManager.createOntology(axioms)

    val isCons = isConsistent(ontology)

    // Clean up.
    ontologyManager.removeOntology(ontology)

    isCons
  }

  /** This method returns `true` iff the given set of set of axioms is
    * consistent.
    *
    * The ontology manager is used to create an ontology consisting of the
    * provided axioms and then a reasoner is used to check for consistency.
    *
    * Each set represents one point in time and in the ontology creation
    * process, flexible names are replaced by time-stamped copies.
    *
    * @param ontologyManager
    *   The OWL ontology manager.
    * @param axiomsSet
    *   The set of set of axioms to be checked for consistency.
    * @param rigidIRIs
    *   The set of rigid IRIs.
    * @return `true` iff the set of set of axioms is consistent.
    */
  def isSetConsistent(ontologyManager: OWLOntologyManager,
                      axiomsSet: Set[Set[OWLAxiom]],
                      rigidIRIs: Set[IRI]): Boolean = {

    // Helping function for stamping flexible names in OWL axiom.
    def stampFlexibleNames(axiom: OWLAxiom, stamp: Int): OWLAxiom = {

      val df = ontologyManager.getOWLDataFactory

      // Helping function for stamping flexible names in class expressions.
      def stampClsExp(clsExp: OWLClassExpression): OWLClassExpression = {

        clsExp match {

          case c: OWLClass => {
            df.getOWLClass(
              stampIRI(c.getIRI))
          }
          
          case c: OWLObjectAllValuesFrom => {
            df.getOWLObjectAllValuesFrom(
              stampPropExp(c.getProperty),
              stampClsExp(c.getFiller))
          }

          case c: OWLObjectComplementOf => {
            df.getOWLObjectComplementOf(
              stampClsExp(c.getOperand))
          }

          case c: OWLObjectIntersectionOf => {
            df.getOWLObjectIntersectionOf(
              c.getOperands map (stampClsExp(_)))
          }

          case c: OWLObjectSomeValuesFrom => {
            df.getOWLObjectSomeValuesFrom(
              stampPropExp(c.getProperty),
              stampClsExp(c.getFiller))
          }

          case c: OWLObjectUnionOf => {
            df.getOWLObjectUnionOf(
              c.getOperands map (stampClsExp(_)))
          }

          case _ => clsExp // Do nothing.
        }
      }

      // Helping function for stamping flexible names in property expressions.
      def stampPropExp(propExp: OWLObjectPropertyExpression): OWLObjectPropertyExpression = {

        propExp match {

          case p: OWLObjectInverseOf => {
            df.getOWLObjectInverseOf(
              stampPropExp(p.getInverse))
          }

          case p: OWLObjectProperty => {
            df.getOWLObjectProperty(
              stampIRI(p.getIRI))
          }

          case _ => propExp // Do nothing.
        }
      }

      // Helping function for stamping flexible IRIs.
      def stampIRI(iri: IRI): IRI = {

        if (rigidIRIs.contains(iri)) {
          iri
        } else {
          IRI.create(iri + stamp.toString)
        }
      }

      // Stamp axiom.
      axiom match {

        // CASE: C(a)
        case ax: OWLClassAssertionAxiom => {
          df.getOWLClassAssertionAxiom(
            stampClsExp(ax.getClassExpression),
            ax.getIndividual)
        }
        
        // CASE: ¬r(a,b)
        case ax: OWLNegativeObjectPropertyAssertionAxiom => {
          df.getOWLNegativeObjectPropertyAssertionAxiom(
            stampPropExp(ax.getProperty),
            ax.getSubject,
            ax.getObject)
        }

        // CASE: r(a,b)
        case ax: OWLObjectPropertyAssertionAxiom => {
          df.getOWLObjectPropertyAssertionAxiom(
            stampPropExp(ax.getProperty),
            ax.getSubject,
            ax.getObject)
        }

        // CASE: C ⊑ D
        case ax: OWLSubClassOfAxiom => {
          df.getOWLSubClassOfAxiom(
            stampClsExp(ax.getSubClass),
            stampClsExp(ax.getSuperClass))
        }

        // CASE: _
        case _ => axiom // Do nothing.
      }
    }

    // Compute set of new axioms by stamping flexible names.
    var time = 0
    val newAxioms = axiomsSet flatMap { axSet => {

        time += 1
        axSet map (stampFlexibleNames(_, time))
      }
    }

    // Return whether set of new axioms is consistent.
    isConsistent(ontologyManager, newAxioms)
  }
}

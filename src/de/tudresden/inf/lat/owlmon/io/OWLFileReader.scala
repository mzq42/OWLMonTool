package de.tudresden.inf.lat.owlmon.io

import scala.collection.JavaConversions._

import scala.collection.mutable.Map
import scala.collection.mutable.Set

import org.semanticweb.owlapi.model.IRI
import org.semanticweb.owlapi.model.OWLAnnotationAssertionAxiom
import org.semanticweb.owlapi.model.OWLAxiom
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom
import org.semanticweb.owlapi.model.OWLNegativeObjectPropertyAssertionAxiom
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom
import org.semanticweb.owlapi.model.OWLOntology
import org.semanticweb.owlapi.model.OWLOntologyCreationException
import org.semanticweb.owlapi.model.OWLOntologyManager

/** This object is used to read ontologies from OWL files.
  *
  * @author Marcel Lippmann
  */
object OWLFileReader {

  // The current number of individuals.
  private[this] var indNr: Int = 0

  /** This method is used to read an OWL ontology from a given IRI.
    *
    * It returns a pair consisting of a translation map, i.e. a map from
    * `String` to `OWLAxiom` where `s` is mapped to `a` iff axiom `a` was read
    * and labelled with `s`, and a set of rigid IRIs.
    *
    * @param ontologyManager
    *   The ontology manager.
    * @param documentIRI
    *   The IRI of the document to be read.
    * @return A pair of the translation map and the set of rigid IRIs.
    * @throws OWLFileReaderException
    *   This exception is thrown if the OWL file with the provided IRI cannot
    *   be read.
    */
  def readOWLFile(ontologyManager: OWLOntologyManager,
                  documentIRI: IRI): (Map[String, OWLAxiom], Set[IRI]) = {

    val ontology =
      try {
        ontologyManager.loadOntology(documentIRI)
      } catch {
        case _: OWLOntologyCreationException =>
          throw new OWLFileReaderException(
            "Could not read from the OWL file with IRI: " +
            documentIRI)
      }

    // Consider all read axioms.

    val dataFactory = ontologyManager.getOWLDataFactory

    // Initialise translation map with: <SIGMA> -> Top is_subsumed_by Top.
    val translationMap = Map[String, OWLAxiom](
      "<SIGMA>" -> dataFactory.getOWLSubClassOfAxiom(
                     dataFactory.getOWLThing(), dataFactory.getOWLThing()))

    // Initialise set of rigid IRIs.
    val rigidIRIs = Set[IRI]()

    // Function for retrieving the label.
    def getLabel(axiom: OWLAxiom): Option[String] = {

      (axiom.getAnnotations find (_.getProperty.isLabel)
                            map (_.getValue.toString)
                            map (s => s.substring(1, s.length - 1)))
    }
    
    // Go through all read axioms and perform pattern matching.
    ontology.getAxioms foreach { _ match {

        // CASE: name annotated as rigid.
        case ax: OWLAnnotationAssertionAxiom => {

          // Check for rigid names.
          if (ax.getProperty.isLabel &&
              ax.getValue.toString == "\"rigid\"") {

            ax.getSubject match {
              case iri: IRI => rigidIRIs += iri
              case _ => // Do nothing.
            }
          }
        }

        // CASE: C(a)
        case ax: OWLClassAssertionAxiom => {

          getLabel(ax) match {
            case None => // Do nothing.
            case Some(label) => {
              // Add axiom and complement to map.
              translationMap += label -> ax
              val complAx = dataFactory.getOWLClassAssertionAxiom(
                              dataFactory.getOWLObjectComplementOf(
                                ax.getClassExpression),
                              ax.getIndividual)
              translationMap += ("!" + label) -> complAx
            }
          }
        }

        // CASE: ¬r(a,b)
        case ax: OWLNegativeObjectPropertyAssertionAxiom => {

          getLabel(ax) match {
            case None => // Do nothing.
            case Some(label) => {
              // Add axiom and complement to map.
              translationMap += label -> ax
              val complAx = dataFactory.getOWLObjectPropertyAssertionAxiom(
                              ax.getProperty,
                              ax.getSubject,
                              ax.getObject)
              translationMap += ("!" + label) -> complAx
            }
          }
        }

        // CASE: r(a,b)
        case ax: OWLObjectPropertyAssertionAxiom => {

          getLabel(ax) match {
            case None => // Do nothing.
            case Some(label) => {
              // Add axiom and complement to map.
              translationMap += label -> ax
              val complAx = dataFactory.getOWLNegativeObjectPropertyAssertionAxiom(
                              ax.getProperty,
                              ax.getSubject,
                              ax.getObject)
              translationMap += ("!" + label) -> complAx
            }
          }
        }

        // CASE: C ⊑ D
        case ax: OWLSubClassOfAxiom => {

          getLabel(ax) match {
            case None => // Do nothing.
            case Some(label) => {
              // Add axiom and complement to map.
              translationMap += label -> ax
              // Complement of C ⊑ D is (C ⊓ ¬D)(aHelp).
              val ind = dataFactory.getOWLNamedIndividual(
                          IRI.create("owlmon:aHelp" + indNr))
              indNr += 1
              val complAx = dataFactory.getOWLClassAssertionAxiom(
                              dataFactory.getOWLObjectIntersectionOf(
                                ax.getSubClass,
                                dataFactory.getOWLObjectComplementOf(
                                  ax.getSuperClass)),
                              ind)
              translationMap += ("!" + label) -> complAx
            }
          }
        }
        
        // CASE: _
        case _ => // Do nothing.
      }
    }

    (translationMap, rigidIRIs)
  }
}

/** This class labels exceptions that occur while using the
  * `OWLFileReader` object.
  *
  * @author Marcel Lippmann
  */
class OWLFileReaderException(message: String)
  extends RuntimeException(message)

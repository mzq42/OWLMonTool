package de.tudresden.inf.lat.owlmon.main

import scala.collection.JavaConversions._

import scala.collection.mutable.Map
import scala.collection.mutable.Set

import java.io.File

import org.semanticweb.owlapi.apibinding.OWLManager

import org.semanticweb.owlapi.model.IRI

import de.tudresden.inf.lat.owlmon.datastructures.ALCLTLFormula

import de.tudresden.inf.lat.owlmon.io.OWLFileReader

import de.tudresden.inf.lat.owlmon.monitoring.BuechiAutomaton
import de.tudresden.inf.lat.owlmon.monitoring.Monitor

object Main extends App {

  val inputDir = new File("input").getAbsolutePath
  
  val ontManager = OWLManager.createOWLOntologyManager

  val iri = IRI.create("file://" + inputDir + "/test.owl")

  val (transMap, rigidIRIs) = OWLFileReader.readOWLFile(ontManager, iri)

  val propAbsFormula =
    //"p2 && p3"
    //"((p2 U p4) U p3) U p5"
    //"[](p3 -> ((!p2) U p5))"
    //"<>p1"
    "[](!p2 && !p3 && !p4 && !p5)"
    //"[](true)"
    //"(((((((((p3 U p2) U p4) U p5) U p3) U p2) U p3) U p4) U p1) U p3) U p2" // 10 untils
    //"(((((((((((p3 U p2) U p4) U p5) U p3) U p2) U p1) U p3) U p4) U p3) U p1) U p3) U p2" // 12 untils
    //"XX(p3 && p4 && p5)"
    //"XX p3"
    //"[]<>(p3 && p5) && []<>p4 || XX(p3 && p4 && p5)"

  // Restrict transMap to symbols occurring in propAbsFormula.
  val translationMap = Map() ++ (transMap filterKeys (k => {
      k == "<SIGMA>" ||
      propAbsFormula.indexOf(
        if (k.startsWith("!")) {
          k.substring(1)
        } else {
          k
        }
      ) >= 0
  }))

  val formula = new ALCLTLFormula(propAbsFormula, ontManager, translationMap, rigidIRIs)

  //val constraints = new ALCLTLFormula("[]p4", ontManager, translationMap, rigidIRIs)
  
  //val globalOnt = ontManager.createOntology
  //ontManager.addAxiom(globalOnt, translationMap.get("p5").get)

  val mon = new Monitor(formula) //, globalOnt, constraints)

  //println(">>>STATE: " + mon.currentState)
  //println("   Output: " + mon.getCurrentStateOutput)

  val emptyOnt = ontManager.createOntology

  val start = System.currentTimeMillis
  for (i <- 1 to 10) {

    //println("<<<Read empty ontology")

    //val start = System.currentTimeMillis

    mon.makeStep(emptyOnt)

    //val end = System.currentTimeMillis
    //val diff = end - start
    //println("Step made in: " +
    //  "%d min, %d.%d sec".format(
    //    (diff / 1000) / 60, (diff / 1000) % 60, diff % 1000))
    
    //println(">>>STATE size: " + mon.currentState._1.size + ", " + mon.currentState._2.size)

    //println(">>>STATE: " + mon.currentState)
    //println("   Output: " + mon.getCurrentStateOutput)
  }
  println(">>>STATE size: " + mon.currentState._1.size + ", " + mon.currentState._2.size)
  val end = System.currentTimeMillis
  val diff = end - start
  println("100 trivial steps made in: " +
    "%d min, %d.%d sec".format(
    (diff / 1000) / 60, (diff / 1000) % 60, diff % 1000))
}

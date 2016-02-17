/*********************************************
 * OPL 12.6.3.0 Model
 * Author: patrickmesana
 * Creation Date: 2016-02-10 at 9:17:54 PM
 *********************************************/

int nbrAvionsMax = ...;
range avions = 1..nbrAvionsMax;

int nbrProduitsMax = ...;
range produits = 1..nbrProduitsMax;

float avionMasseMax = ...;
float ACD[1..3] = ...;
float PQ[produits] = ...;
float PV[produits] = ...;


// ***********************
// Variables de decision
// ***********************
dvar int+ avion[avions];
dvar int+ a[avions][produits];
dvar int+ c[avions][produits];
dvar int+ d[avions][produits];
dvar float+ qa[avions][produits];
dvar float+ qc[avions][produits];
dvar float+ qd[avions][produits];
// ***********************
// Fonction-objectif
// ***********************


minimize sum (a in avions) avion[a];
 
// ***********************
// Contraintes
// ***********************



dexpr int arriere[i in avions] = sum(p in produits) a[i][p];
dexpr int centre[i in avions] = sum(p in produits) c[i][p];
dexpr int devant[i in avions] = sum(p in produits) d[i][p];

dexpr float arriereEnTonnes[i in avions] = sum(p in produits) qa[i][p];
dexpr float centreEnTonnes[i in avions] = sum(p in produits) qc[i][p];
dexpr float devantEnTonnes[i in avions] = sum(p in produits) qd[i][p];

dexpr float arriereEnM3[i in avions] = sum(p in produits) qa[i][p] * PV[p];
dexpr float centreEnM3[i in avions] = sum(p in produits) qc[i][p] * PV[p];
dexpr float devantEnM3[i in avions] = sum(p in produits) qd[i][p] * PV[p];

subject to{
	
	//1 avion ne peut etre emprunter qu'une seule fois au plus
	forall (i in avions, p in produits){
		avion[i] <= 1;
	}
	
	//Un seul type de produit par compartiment
	forall (i in avions){
		arriere[i] <= 1;
		centre[i] <= 1; 
		devant[i] <= 1;
	}
	  
	//Ai, Ci, et Di forment un avion de 3 compartiments
	forall (i in avions){
		avion[i] == 0 => (arriere[i] == 0 && centre[i] == 0 && devant[i] == 0);
		avion[i] == 1 => (arriere[i] == 1 || centre[i] == 1 || devant[i] == 1);
	}
	
	//La demande
	forall (p in produits) {
		sum(i in avions) qa[i][p] + 
		sum(i in avions) qc[i][p] +
		sum(i in avions) qd[i][p] == PQ[p]; 
	}
	
	//La masse d'un produit dans un compartiment est au plus 100
	forall (i in avions, p in produits){
		qa[i][p]	<= avionMasseMax * a[i][p];
		qc[i][p]	<= avionMasseMax * c[i][p];
		qd[i][p]	<= avionMasseMax * d[i][p];
	}
	
	//La masse total des compartiements est au plus 100
	forall (i in avions) {
		arriereEnTonnes[i] + centreEnTonnes[i] + devantEnTonnes[i] <= avionMasseMax;
	}
	
	//Chaque compartiment a une limite de volume 
	forall (i in avions){
		arriereEnM3[i] <= ACD[1];
		centreEnM3[i] <= ACD[2];
		devantEnM3[i] <= ACD[3];	
	}
		
	//Le centre doit etre plus lourd que l'arriere et le devant
	forall (i in avions){
		centreEnTonnes[i] >= arriereEnTonnes[i] &&
		centreEnTonnes[i] >= devantEnTonnes[i];
	}
	 
	//L'ecart de masse entre le chargement de devant et celui de
	//derriere ne doit pas depasser 10 tonnes 
	forall (i in avions){
		abs(arriereEnTonnes[i] - devantEnTonnes[i]) <= 10;	
	}
	
	//P1 et P3 ne peuvent pas etre adjacents
	forall (i in avions){
		a[i][1] + c[i][3] <= 1;
		a[i][3] + c[i][1] <= 1;
		c[i][1] + d[i][3] <= 1;
		c[i][3] + d[i][1] <= 1;
	}
	
	//P7 et P13 ne peuvent pas etre adjacents
	forall (i in avions){
		a[i][7] + c[i][13] <= 1;
		a[i][13] + c[i][7] <= 1;
		c[i][7] + d[i][13] <= 1;
		c[i][13] + d[i][7] <= 1;
	}
	
    //P6 et P12 ne peuvent pas se retrouver dans le meme avions
	forall (i in avions){
		a[i][6] + c[i][12] <= 1;
		a[i][12] + c[i][6] <= 1;
		c[i][6] + d[i][12] <= 1;
		c[i][12] + d[i][6] <= 1;
		d[i][12] + a[i][6] <= 1;
		a[i][12] + d[i][6] <= 1;
	}
	
};


//Script pour ecrire la solution optimale
execute{

	var ajs = new Array(nbrAvionsMax);
	var cjs = new Array(nbrAvionsMax);
	var djs = new Array(nbrAvionsMax);
	var aqs = new Array(nbrAvionsMax);
	var cqs = new Array(nbrAvionsMax);
	var dqs = new Array(nbrAvionsMax);
	
	for (var i in avions) {
		for (var j in produits) {
			if(a[i][j] > 0) {
				ajs[i] = j;	
				aqs[i] = qa[i][j];		
			} 	
			if(c[i][j] > 0) {
				cjs[i] = j;	
				cqs[i] = qc[i][j];		
			} 
			if(d[i][j] > 0) {
				djs[i] = j;	
				dqs[i] = qd[i][j];	
			} 	
		}
	}
	
	writeln("Readable Version: ")
	for (var i in avions) {
		var astr = "empty", cstr = "empty", dstr = "empty";
		if (ajs[i] > 0 && aqs[i] > 0) astr = "P" + ajs[i] + ":" + aqs[i];
		if (cjs[i] > 0 && cqs[i] > 0) cstr = "P" + cjs[i] + ":" + cqs[i];	
		if (djs[i] > 0 && dqs[i] > 0) dstr = "P" + djs[i] + ":" + dqs[i];	
		
		if (ajs[i] > 0 || cjs[i] > 0 || djs[i] > 0) 
		   writeln(astr + " | " + cstr + " | " + dstr);
	   
  	}	 
  	
  	writeln(" \nCSV Products: ")
  	for (var i in avions) {
		var astr = "", cstr = "", dstr = "";
		if (ajs[i] > 0 && aqs[i] > 0) astr = ajs[i];
		if (cjs[i] > 0 && cqs[i] > 0) cstr = cjs[i];	
		if (djs[i] > 0 && dqs[i] > 0) dstr = djs[i];	
		
		if (ajs[i] > 0 || cjs[i] > 0 || djs[i] > 0) 
		   writeln(astr + "," + cstr + "," + dstr);
	   
  	}	  
		
	writeln(" \nCSV Quantities: ")
  	for (var i in avions) {
		var astr = "", cstr = "", dstr = "";
		if (ajs[i] > 0 && aqs[i] > 0) astr = aqs[i];
		if (cjs[i] > 0 && cqs[i] > 0) cstr = cqs[i];	
		if (djs[i] > 0 && dqs[i] > 0) dstr = dqs[i];	
		
		if (ajs[i] > 0 || cjs[i] > 0 || djs[i] > 0) 
		   writeln(astr + "," + cstr + "," + dstr);
	   
  	}
}
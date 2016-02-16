/*********************************************
 * OPL 12.6.3.0 Model
 * Author: patrickmesana
 * Creation Date: 2016-02-10 at 9:17:54 PM
 *********************************************/

int nbrAvionsMax = ...;
range avions = 1..nbrAvionsMax;

int nbrProduitsMax = ...;
range produits = 1..nbrProduitsMax;

int nbrCompartimentsMax = ...;
range compartiments = 1..nbrCompartimentsMax;

//prend la valeur haute dans le cas d'un nombre impair, n = 3 => cDuMilieu = 2
int compartimentDuMilieu = (nbrCompartimentsMax + 1) div 2;

float avionMasseMax = ...;
float ACD[1..3] = ...;
float PQ[produits] = ...;
float PV[produits] = ...;

// ***********************
// Variables de decision
// ***********************
dvar int+ avion[avions];
dvar int+ compartiment[avions][compartiments][produits];
dvar float+ compartiment_quantity[avions][compartiments][produits];

// ***********************
// Fonction-objectif
// ***********************
minimize sum (a in avions) avion[a];
 
// ***********************
// Contraintes
// ***********************

dexpr int compartimentEnNbr[i in avions][c in compartiments]
 	= sum(p in produits) compartiment[i][c][p];

dexpr float compartimentEnTonnes[i in avions][c in compartiments]
 	= sum(p in produits) compartiment_quantity[i][c][p];

dexpr float compartimentEnM3[i in avions][c in compartiments]
 	= sum(p in produits) compartiment_quantity[i][c][p] * PV[p];

dexpr int produitsDesCompartiments[i in avions] = max(c in compartiments, p in produits) compartiment[i][c][p];
dexpr int sommeDesCompartiments[i in avions] = sum(c in compartiments, p in produits) compartiment[i][c][p];

subject to{
	
	//1 avion ne peut etre emprunter qu'une seule fois au plus
	forall (i in avions){
		avion[i] <= 1;
	}
	
	//Un seul type de produit par compartiment
	forall (i in avions, c in compartiments){
		compartimentEnNbr[i][c] <= 1;
	}


	//Ai, Ci, et Di forment un avion de 3 compartiments
	forall (i in avions){
		avion[i] == 0 => produitsDesCompartiments[i] == 0;
		avion[i] == 1 => sommeDesCompartiments[i] >= 1;
	}
	
	//La demande
	forall (p in produits) {		
		sum(i in avions, c in compartiments) compartiment_quantity[i][c][p] == PQ[p];
	}
	
	//La masse d'un produit dans un compartiment est au plus 100
	//Cree une relation entre les deux variables de decisions.
	//La quantite depend maintenant de si la variable binaire est 1 ou 0
	forall (i in avions, p in produits, c in compartiments){
		compartiment_quantity[i][c][p] <= avionMasseMax * compartiment[i][c][p];
	}
	
	//La masse total des compartiements est au plus 100
	forall (i in avions) {
		sum(c in compartiments) compartimentEnTonnes[i][c] <= avionMasseMax;
	}
	
	//Chaque compartiment a une limite de volume 
	forall (i in avions, c in compartiments){
		compartimentEnM3[i][c] <= ACD[c];
	}
		
	//Le centre doit etre plus lourd que l'arriere et le devant
	forall (i in avions){
		compartimentEnTonnes[i][compartimentDuMilieu] >= compartimentEnTonnes[i][1] &&
		compartimentEnTonnes[i][compartimentDuMilieu] >= compartimentEnTonnes[i][nbrCompartimentsMax];
	}
	 
	//L'ecart de masse entre le chargement de devant et celui de
	//derriere ne doit pas depasser 10 tonnes 
	forall (i in avions){
		abs(compartimentEnTonnes[i][1] - compartimentEnTonnes[i][nbrCompartimentsMax]) <= 10;	
	}
	
	//P1 et P3 ne peuvent pas etre adjacents quand 3 compartiments
	forall (i in avions){
		compartiment[i][1][1] + compartiment[i][compartimentDuMilieu][3] <= 1;
		compartiment[i][1][3] + compartiment[i][compartimentDuMilieu][1] <= 1;
		compartiment[i][compartimentDuMilieu][1] + compartiment[i][nbrCompartimentsMax][3] <= 1;
		compartiment[i][compartimentDuMilieu][3] + compartiment[i][nbrCompartimentsMax][1] <= 1;
	}
	
	//P7 et P13 ne peuvent pas etre adjacents quand 3 compartiments
	forall (i in avions){
		compartiment[i][1][7] + compartiment[i][compartimentDuMilieu][13] <= 1;
		compartiment[i][1][13] + compartiment[i][compartimentDuMilieu][7] <= 1;
		compartiment[i][compartimentDuMilieu][7] + compartiment[i][nbrCompartimentsMax][13] <= 1;
		compartiment[i][compartimentDuMilieu][13] + compartiment[i][nbrCompartimentsMax][7] <= 1;
	}
	
    //P6 et P12 ne peuvent pas se retrouver dans le meme avions quand 3 compartiments
	forall (i in avions){
		compartiment[i][1][6] + compartiment[i][compartimentDuMilieu][12] <= 1;
		compartiment[i][1][12] + compartiment[i][compartimentDuMilieu][6] <= 1;
		compartiment[i][compartimentDuMilieu][6] + compartiment[i][nbrCompartimentsMax][12] <= 1;
		compartiment[i][compartimentDuMilieu][12] + compartiment[i][nbrCompartimentsMax][6] <= 1;
		compartiment[i][nbrCompartimentsMax][12] + compartiment[i][1][6] <= 1;
		compartiment[i][1][12] + compartiment[i][nbrCompartimentsMax][6] <= 1;
	}
	
};

//Script pour ecrire la solution optimale
execute{
	for (var i in avions) {
		var compartiments_j = new Array(nbrCompartimentsMax);
		var compartiments_quantity_j = new Array(nbrCompartimentsMax);
		for (var j in produits) {
			for (var c in compartiments) {
				if(compartiment[i][c][j] > 0) {
				compartiments_j[c] = j;	
				compartiments_quantity_j[c] = compartiment_quantity[i][c][j];		
				} 		
			}		 	
		}
		
		//Readable Version
//		var compartiments_str = new Array(nbrCompartimentsMax);
//		for (var c in compartiments) {
//			compartiments_str[c] = "empty";	
//		}
//		
//		for (var c in compartiments) {
//			if (compartiments_j[c] > 0 && compartiments_quantity_j[c] > 0)		
//				compartiments_str[c] = "P" + compartiments_j[c] + ":" + compartiments_quantity_j[c];	
//		}
//			
//		var isPlainNonEmpty = false;
//		for (var c in compartiments) {
//			isPlainNonEmpty = isPlainNonEmpty || compartiments_j[c] > 0;		
//		}
//		
//		if (isPlainNonEmpty) {
//			var strFinal = "";
//			for (var c in compartiments) {
//				strFinal += compartiments_str[c];
//				if (c < nbrCompartimentsMax) {
//					strFinal += " | ";			
//				}		
//			}
//			writeln(strFinal);
//		}  
		
		//CVS Version
		var compartiments_str = new Array(nbrCompartimentsMax);
		for (var c in compartiments) {
			compartiments_str[c] = "";	
		}
		
		for (var c in compartiments) {
			if (compartiments_j[c] > 0 && compartiments_quantity_j[c] > 0)		
				compartiments_str[c] = compartiments_quantity_j[c];	
		}
			
		var isPlainNonEmpty = false;
		for (var c in compartiments) {
			isPlainNonEmpty = isPlainNonEmpty || compartiments_j[c] > 0;		
		}
		
		if (isPlainNonEmpty) {
			var strFinal = "";
			for (var c in compartiments) {
				strFinal += compartiments_str[c];
				if (c < nbrCompartimentsMax) {
					strFinal += ",";			
				}		
			}
			writeln(strFinal);
		} 
	}
		
}
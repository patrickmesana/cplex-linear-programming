/*********************************************
 * OPL 12.6.3.0 Model
 * Author: patrickmesana
 * Creation Date: 2016-02-21 at 4:04:39 PM
 *********************************************/

 // Ensemble de N noeuds à visiter 
int     N       = ...;
int nbrDeCamions = 3;
range camions = 1..nbrDeCamions;
int tourneeMax = 15;
range   V  = 1..N;
int tempsMax = 420; //7heures

// Ensemble d'arcs (cas asymetrique)
tuple       arc        {int v_dep; int v_arr;}
setof(arc) A     = {<i,j> | i,j in V: i != j};

// Matrice de distance
float         D[V][V] = ...;

// ***********************
// Variables de decision
// ***********************

// x [<i,j>]= 1 si le noeud j suit immédiatement le noeud i  dans le circuit
dvar boolean x[camions][A];

// Variables de flot pour elimination de sous-tours
dvar float+ y[camions][A];

// ***********************
// Fonction-objectif
// ***********************

// Minimiser la longueur du circuit
minimize sum (<i,j> in A, c in camions) D[i][j]*x[c][<i,j>];

dexpr float sommeTournee[c in camions] = sum (a in A) D[a.v_dep][a.v_arr]*x[c][a];

// ***********************
// Contraintes
// ***********************
subject to {
   
   forall (v in V: v != 1){
   		// On entre dans chaque noeud une et une seule fois   
        sum (a in A, c in camions: a.v_arr == v) x[c][a] == 1;
        // On sort de chaque noeud une et une seule fois
        sum (a in A, c in camions: a.v_dep == v) x[c][a] == 1;
   }
   
 	//Autorise 3 entrees et 3 sorties du noeud initiale
    sum (a in A, c in camions: a.v_arr == 1) x[c][a] == 3;
    sum (a in A, c in camions: a.v_dep == 1) x[c][a] == 3;

   //Un camion ne peut utiliser le noeud initial qu'une fois
   forall (c in camions){
        // On entre du noeud 1 une et une seule fois   
        sum (a in A: a.v_arr == 1) x[c][a] == 1;
        // On sort du noeud 1 une et une seule fois
        sum (a in A: a.v_dep == 1) x[c][a] == 1;
   }
   
   //Un camion qui va a un noeud doit en resortir
    forall (c in camions, v in V) {
            sum (a in A: a.v_arr == v) x[c][a] - sum (a in A: a.v_dep == v) x[c][a] == 0; 
        }
        
    // Elimination de sous-tours par les variables de flot   
 	forall (c in camions, v in V:v != 1){
 	 	sum (a in A: a.v_arr == v) y[c][a] - sum (a in A: a.v_dep == v) y[c][a] == sum (a in A: a.v_arr == v) x[c][a];
 	}
 	  
 	// Chaque tournee peut aller jusqua max 15 clients  
 	forall (c in camions){
 		sum (a in A: a.v_arr == 1) y[c][a] - sum (a in A: a.v_dep == 1) y[c][a] >= -(tourneeMax-1);
	} 	
 	 	
 	// Si x est 0 y est 0, sinon x peut prendre une valeure max  
 	forall (c in camions, a in A){
 	    y[c][a] <= tourneeMax*x[c][a];
    } 	  
   
    //Chaque tournee doit se faire en moins de 7heures (420minutes)
   	forall (c in camions){
   		sommeTournee[c] <= tempsMax;
    }  
 };

// Affichage de la solution optimale 
 setof(int) succ[c in camions,i in V] = {j | <i,j> in A : x[c][<i,j>] == 1};
   execute{   
   
    function compactTournee(tourneeContainer, tourneeEnds) {
	     var t = new Array(tourneeEnds + 1);
	     for (var k = 0; k < tourneeEnds + 1; k++) {
	          t[k] = tourneeContainer[k];
	     }
	     return t;
     }   
     
    function writeTournee(tourneeContainer) {
	    write("1");
	    for (var k = 0; k < tourneeContainer.length - 1; k++) {
	    	write(",", tourneeContainer[k]);
	    }
	    write(",", tourneeContainer[tourneeContainer.length - 1]);
    } 
     
    var noeudsCouverts = 0;
    for (var it = 1; it < nbrDeCamions + 1; it++)
    { 
		  var tournee = new Array();
		  var tourneeIndex = 0;
		  for (var v = 1; Opl.first(succ[it][v]) != 1 ;)
		  {
		     if (succ[it][v].size > 0)
		     {
			     v = Opl.first(succ[it][v]);
			     tournee[tourneeIndex] = v;
			     tourneeIndex++;
		     }         
		  }
		  tournee[tourneeIndex] = Opl.first(succ[it][v]);
		  writeTournee(compactTournee(tournee, tourneeIndex));
		  writeln();
		  noeudsCouverts += tourneeIndex;
		  
 	 }
 	 writeln("Nbr de noeuds couverts par les tournees: " + (noeudsCouverts + 1));          
};
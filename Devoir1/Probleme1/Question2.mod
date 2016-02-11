/*********************************************
 * OPL 12.6.3.0 Model
 * Author: patrickmesana
 * Creation Date: 2016-02-05 at 5:53:18 PM
 *********************************************/

// ***********************
// Parametres et ensembles
// ***********************

setof(string) F = ...; 
setof(string) U = ...; 
setof (string) C =...; 

// Fournisseur
int fournisseurs [F] = ...;
int fournisseurs_CA [F] = ...;

// Usine
int usines [U] = ...; 
int usines_CA [U] = ...;

// Usine
int centres [C] = ...;

// Matrices de couts
float CFU[F,U] = ...; 
float CUC[U,C] = ...; 

// fournisseur totale
float fournisseurs_tot = sum (i in F) fournisseurs[i];

// usine totale
float usines_tot = sum (i in U) usines[i];

// centre totale
float centres_tot = sum (i in C) centres[i];

// ***********************
// Variables de decision
// ***********************
// Variables de flot
dvar float+ x[F,U];
dvar float+ y[U,C];


// ***********************
// Fonction-objectif
// ***********************
dexpr float cost =
 	sum (i in F, j in U) (CFU[i][j] + fournisseurs_CA[i]) * x[i][j] +
 	 sum (i in U, j in C) (CUC[i][j] + usines_CA[i]) * y[i][j];

minimize cost;

dexpr float prod_total = sum (u in U, c in C) y[u][c];


// ***********************
// Contraintes
// ***********************
subject to{
  forall (f in F)
   
  forall (f in F)
    //Pour tous les fournisseurs on utise au plus l'offre max du fournisseur
    Fournisseurs:
		sum (u in U) x[f][u] <= fournisseurs[f];

  forall (u in U)
    Usines_F: 
     // Pour toutes les usines on ne depasse pas la capacite max de l'usine 
      sum (f in F) x[f][u] <= usines[u] * 5;
   
  forall (i in U)
    Usines_C: 
     // Pour toutes les usines on ne depasse pas la capacite max de l'usine, par raport a la demande
      sum (j in C) y[i][j] <= usines[i];         
      
  forall (j in C)
    Centres: 
     // Pour tous les centre on arrive exactement a la demande
      sum (i in U) y[i][j] == centres[j]; 
     
     
  forall (i in U) 
    Usines_prod:   
    // Pour toutes les usines ce qui sort est exactemnt egale a ce qui entre
      sum (f in F) x[f][i] == 5 * sum(j in C) y[i][j];
      
      
   forall (u in U, c in C) 
   // Chaque centre ne peut recevoir d'une meme usine que 70% de sa demande
    SeventyPercentDemand:   
   	y[u][c] <= 0.7 * centres[c];
          
  forall (u in U, f in F) 
    // Chaque usine ne peut recevoir d'un meme fournisseur qu'au plus 40% de son utilisations totale de MP
      	FourtyPercentProd:  
      	x[f][u] <= 2 * sum (c in C) y[u][c]; // 40% * 5 * capacity => 2 * capacity
      
      
  forall (u1 in U, u2 in U)
      // L'ecart de production entre 2 usines ne peut pas exceder 10% de la production totale
      TenPercentTotal:
      if(u1 != u2) {
     	 abs(sum (c in C) y[u1][c] - sum (c in C) y[u2][c]) <= 0.1 * prod_total;
      }      
    
};


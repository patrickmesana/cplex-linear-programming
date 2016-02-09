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
minimize sum (i in F, j in U) (CFU[i][j] + fournisseurs_CA[i]) * x[i][j] + sum (i in U, j in C) (CUC[i][j] + usines_CA[i]) * y[i][j];


// ***********************
// Contraintes
// ***********************
subject to{
  forall (i in F)
    Fournisseurs:
      if (fournisseurs_tot > (usines_tot * 5))
         sum (j in U) x[i][j] <= fournisseurs[i];
      else
         sum (j in U) x[i][j] == fournisseurs[i];

  forall (j in U)
    Usines_F: 
     if ((usines_tot * 5) > fournisseurs_tot)
        sum (i in F) x[i][j] <= usines[j] * 5;
     else
      sum (i in F) x[i][j] == usines[j] * 5;
   
  forall (i in U)
    Usines_C: 
     if (usines_tot > centres_tot) {
        sum (j in C) y[i][j] <= usines[i];
        sum (f in F) x[f][i] >= 5 * sum(j in C) y[i][j];
     }        
     else {
      sum (j in C) y[i][j] == usines[i];  
      sum (f in F) x[f][i] == 5 * sum(j in C) y[i][j];
    }      
      
  forall (j in C)
    Centres: 
     if (centres_tot > usines_tot)
        sum (i in U) y[i][j] <= centres[j];
     else
      sum (i in U) y[i][j] == centres[j]; 
      
      
      
};


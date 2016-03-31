/*********************************************
 * OPL 12.6.3.0 Model
 * Author: patrickmesana
 * Creation Date: 2016-03-26 at 7:32:54 PM
 *********************************************/

 int vendredi = ...;
 int nrbAP = ...;
 int nbrAS = ...;
 range jours = 1..vendredi;
 float analyses[jours] = ...;
 int CAP = ...; // Cout par jour d'un Analyste Permanent (AP)
 int CAS = ...; // Cout par jour d'un Analyste Surnumenaire (AS)
 int CHSP = ...; // Cout Heure Sup d'un AP
 int CHSS = ...; // Cout Heure Sup d'un AS
 int RAP = ...; // Rendement d'un AP
 int RAS = ...; // Rendement d'un AS
 int coutDeDepassement = ...;
 
 //Params Stoquastiques
 int nbrDeScenarios = ...;
 int nbrDeSequences = 243; //3^5
 range seqs = 1..nbrDeSequences; 
 int sequences[seqs][jours];
 int nb_seq = nbrDeSequences;
 int N = vendredi; 
 int M = nbrDeScenarios;
 //Ensemble de scenarios (identique pour chaque periode)
 range S = 1..M;
 //Probabilite de chaque scenario pour chaque periode
 float Probabilite[S] = ...;
 //Probabilite de chaque sequence
 float P[1..nb_seq]; 
 range apGroups = 1..5;
 int combinaisonJoursAP[apGroups][jours] = ...;
 float An[jours][S];
 
 // Parametres A[t][i][j] = 1 si les sequences i et j partagent le meme 
 // historique a la periode t
  int A[jours][1..nb_seq][1..nb_seq];
  
 execute{

 // Remplissage d'une matrice avec toutes les sequences possibles 
	for (var i=1 ; i<= nb_seq ; i++)
		for (var j=1 ; j<= N ; j++)
		{
      		sequences[i][j] = 1 + (Opl.floor(((i-1)/(Opl.pow(M,N-j))))%M);
		}

 // Calcul de la probabilite de chaque sequence           
   	for (i = 1 ; i <= nb_seq ; i++)
	{
      P[i] = 1.0;
      for (var t = 1; t <= N ; t++)
        P[i] *= Probabilite[sequences[i][t]];   
    }

// Calcule de la demande d'analyses moyennes suivant la demande
    for (var t = 1; t <=N ; t++) {   
       An[t][1] = 0.8 * analyses[t];
       An[t][2] = analyses[t];
       An[t][3] =  0.8 * analyses[t];
    } 
    
      
 // Periode 1 : toutes les sequences ont le meme historique au debut 
	for (var k = 1; k <= nb_seq; k++)
		for (var l = 1; l <= nb_seq; l++)
       	{
             A[1][k][l] = 1;  
       	}          
  
  // Comparer les sequences i et j pour voir si elles possedent le 
  // meme historique a la periode t (t = 2..N)                  
	for (var t = 2; t <= N; t++)
		for (k = 1; k <= nb_seq; k++)
			for (l = 1; l <= nb_seq; l++)
       		{
           		A[t][k][l] = 1; 
            
             	for (var j = 1; j <= t-1; j++)
             	{
               		if (sequences[k][j] != sequences[l][j])
                	{
                  		A[t][k][l] = 0; 
                	}                  
             	}
             } 
} ; 

// ***********************
// Variables de decision
// ***********************
dvar int+ nbrAnP[jours][seqs];
dvar int+ nbrAnS[jours][seqs];
dvar int+ d[apGroups][seqs];
dvar int+ HSp[seqs]; //heures sup d'un AP
dvar int+ HSs[seqs]; //heures sup d'un AS
dvar int+ Stock[jours][seqs];//stock au debut de la journee

 
// ***********************
// Fonction-objectif
// ***********************
minimize sum(s in seqs) P[s] * ( 
		sum (j in jours) nbrAnP[j][s] * CAP +
		sum (j in jours) nbrAnS[j][s] * CAS +
		HSp[s] * CHSP +
		HSs[s] * CHSS + 
		sum (j in jours) Stock[j][s] * coutDeDepassement);
 
// ***********************
// Expressions
// ***********************
//heures d'analyse par AP dans la journee
dexpr int HAP[j in jours, s in seqs] = 7 * nbrAnP[j][s];
//heures d'analyse par AS dans la journee
dexpr int HAS[j in jours, s in seqs] = 7 * nbrAnS[j][s];
//quantite d'analyses traitees dans la journee
dexpr int Q[j in jours, s in seqs] = HAP[j][s] * RAP + HAS[j][s] * RAS;
//quantites sup a traite
dexpr int Qs[s in seqs] = HSp[s] * RAP + HSs[s] * RAS;

subject to {

//On commence la semaine sans stock
forall (s in seqs) Stock[1][s] == 0;

//les stocks est ce qui reste a faire a la fin de la journee
forall (j in 1..vendredi-1, s in seqs) Stock[j+1][s] == (An[j][sequences[s][j]] + Stock[j][s]) - Q[j][s];


//Semaine de 4 jours pour AP
forall(j in jours, s in seqs) sum(g in apGroups) combinaisonJoursAP[j][g] * d[g][s] == nbrAnP[j][s];

//5 AP max en conges par jour et max des deux types
forall (j in jours, s in seqs){ 
	nbrAnP[j][s] >= nrbAP - 5;
	nbrAnP[j][s] <= nrbAP;
	nbrAnS[j][s] <= nbrAS;
}

//heures suplementaires
forall (s in seqs) {
	analyses[vendredi] + Stock[vendredi][s] == Q[vendredi][s] + Qs[s];
	HSp[s] <= nbrAnP[vendredi][s] * 2;
	HSs[s] <= nbrAnS[vendredi][s] * 2;
}

//contraintes de non-anticipations
   forall(t in jours, k in 1..nb_seq)
   non_anticipation_AP:
   sum(l in 1..nb_seq : l != k) (P[l]*A[t][k][l]*nbrAnP[t][l]) ==
   (sum(l in 1..nb_seq : l != k) P[l]*A[t][k][l])*nbrAnP[t][k];  
   
   forall(t in jours, k in 1..nb_seq)
   non_anticipation_AS:
   sum(l in 1..nb_seq : l != k) (P[l]*A[t][k][l]*nbrAnS[t][l]) ==
   (sum(l in 1..nb_seq : l != k) P[l]*A[t][k][l])*nbrAnS[t][k];
}
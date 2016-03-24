/*********************************************
 * OPL 12.6.3.0 Model
 * Author: patrickmesana
 * Creation Date: 2016-03-18 at 3:48:03 PM
 *********************************************/

 int nbrSites = ...;
 int nbrClients = ...;
 range sites = 1..nbrSites;
 range clients = 1..nbrClients;
 int nbrDeFranchisesAOuvrir = ...;
 int clientsDesservisMin = ...;
 int clientsDesservisMax = ...;
 float DistanceCS[clients][sites] = ... ;
 float DistanceSS[sites][sites] = ... ;
 
 tuple       couple        {int s1; int s2;}
 setof(couple) S = {<i,j> | i,j in sites: i != j};


// ***********************
// Variables de decision
// ***********************
dvar boolean x[sites]; //vaut 1 si la franchise est choisi, 0 sinon
dvar boolean y[clients][sites]; //vaut 1 si le client i est desservi par la franchise j, 0 sinon
dvar float v_min;

// ***********************
// Fonction-objectif
// ***********************
maximize v_min;

// ***********************
// Expressions
// *********************** 
dexpr int nbrDeClientsDeservisParLeSite[s in sites] = sum (c in clients) y[c][s]; 
dexpr int nbrDeSitesQuiDeserveLeClient[c in clients] = sum (s in sites) y[c][s]; 
dexpr int nbrDeSitesOuverts = sum(s in sites) x[s];
 
// ***********************
// Contraintes
// ***********************
subject to {
	//Nbr de franchise a ouvrir
	 nbrDeSitesOuverts == nbrDeFranchisesAOuvrir;
	
	//Tous les clients doivent etre desservi au moins 1 fois
	forall (c in clients) nbrDeSitesQuiDeserveLeClient[c] >= 1;
		
	//Un site doit desservir dans un certain range et 
	//Si le site n'est pas ouvert les clients ne peuvent pas etre desservi par ce site
	forall (s in sites) {	
		nbrDeClientsDeservisParLeSite[s] >= clientsDesservisMin * x[s];
		nbrDeClientsDeservisParLeSite[s] <= clientsDesservisMax * x[s];	
	}
	
	forall (c in S) {
		 (x[c.s1] == 1 && x[c.s2] == 1) =>  (v_min <= DistanceSS[c.s1][c.s2]);
	}
		
}

dexpr float z[i in sites][j in sites] = x[i] == 1 && x[j] == 1 && i != j;

execute {
	
	function equalsPair(pair1, pair2) {
		return ((pair1.site1 == pair2.site1) && (pair1.site2 == pair2.site2)) ||
				((pair1.site1 == pair2.site2) && (pair1.site2 == pair2.site1));
	}
	
	function SitePair(site1, site2, distance) {
		this.site1 = site1;
		this.site2 = site2;
		this.distance = distance;	
	}
	
	function isPairAlreadyIn(pairs, pair) {
		for (var i = 0; i < pairs.length; i++) {
			if (equalsPair(pairs[i], pair)) {
				return true;			
			}	
		}
		return false;
	}
	
	var maxLength = nbrDeFranchisesAOuvrir * (nbrDeFranchisesAOuvrir - 1) / 2;
	var results = new Array(maxLength);
	var nextFranchise = 0;
	for (var i = 1; i < nbrSites + 1; i++) {
		for (var j = 1; j < nbrSites + 1; j++) {
			if (z[i][j] == 1) {
				var aSitePair = new SitePair(i, j, DistanceSS[i][j]);
				if (!isPairAlreadyIn(results, aSitePair)) {
					results[nextFranchise] = aSitePair;
					nextFranchise++;			
				}
			}	
		}
	}
	
	for (var i = 0; i < maxLength; i++) {
		writeln('<'+results[i].site1+','+results[i].site2+'> '+results[i].distance);	
	}	
	
	"Nbr de couples de sites: " + maxLength;
}
package polls;

import java.sql.Timestamp;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import politics.Party;
import politics.PoliticalEntity;

public class PollOrdinale extends Poll {
	/*@ invariant candidates != null && votes != null && (\forall int i; i >= 0 && i < candidates.length; candidates[i] != null) &&
	 @ (\forall int j; j >= 0 && j < votes.length; votes[j] != null) 
	 @*/
	private /*@ spec_public @*/ boolean absoluteMajority;
	private List<PoliticalEntity> candidates;
	private List<VoteOrdinale> votes;
	
	public PollOrdinale(String name, String description, Timestamp startDate, Timestamp endDate) {
		super(name, description, startDate, endDate);
		this.absoluteMajority = false;
		candidates = new ArrayList<PoliticalEntity>();
		votes = new ArrayList<VoteOrdinale>();
	}
	
	// @ ensures this.absoluteMajority == absoluteMajority;
	public PollOrdinale(String name, String description, Timestamp startDate, Timestamp endDate, boolean absoluteMajority) {
		super(name, description, startDate, endDate);
		this.absoluteMajority = absoluteMajority;
		candidates = new ArrayList<PoliticalEntity>();
		votes = new ArrayList<VoteOrdinale>();
	}
	
	//@ ensures \result == this.absoluteMajority;
	public boolean getAbsoluteMajority() {
		return absoluteMajority;
	}
	
	//@ requires v != null;
	//@ ensures (\exists int i; i >= 0 && i < votes.size(); votes(i) == v);
	/**
	 * Aggiunge alla lista di voti registrati il voto v fornito come argomento.
	 * @param v: un oggetto di tipo VoteOrdinale
	 */
	public void addVote(VoteOrdinale v) {
		Objects.requireNonNull(v);
		votes.add(v);
	}
	
	//@ requires e != null;
	//@ ensures (\exists int i; i >= 0 && i < candidates.size(); candidates.get(i) == e);
	/**
	 * Aggiunge alla lista di candidati della votazione this il candidato fornito
	 * come argomento se questo non � gi� presente, altrimenti non fa nulla.
	 * @param e: un oggetto PoliticalEntity
	 */
	public void addCandidate(PoliticalEntity e) {
		Objects.requireNonNull(e);
		if(candidates.contains(e)) return;
		candidates.add(e);
	}
	
	//@ requires listOfCandidates != null && (\forall int i; i >= 0 && i < listOfCandidates.length; listOfCandidates[i] != null);
	//@ ensures (\forall int j; j >= 0 && j < listOfCandidates.size(); (\exists int i; i >= 0 && i < candidates.size(); candidates.get(i) == listOfCandidates.get(j)));
	/**
	 * Aggiunge ai candidati gi� registrati nella votazione this quelli presenti
	 * nella lista fornita come argomento escludendo quelli gi� presenti.
	 * @param candidates: una lista di PoliticalEntity
	 */
	public void addCandidate(List<PoliticalEntity> listOfCandidates) {
		Objects.requireNonNull(listOfCandidates);
		for(PoliticalEntity e : listOfCandidates) {
			addCandidate(e);
		}
	}
	
	//@ ensures \result == this.candidates;
	/**
	 * Restituisce la lista di candidati della votazione this.
	 * @return una lista di oggetti PoliticalEntity
	 */
	public List<PoliticalEntity> getCandidates(){
		return candidates;
	}
	
	//@ requires rankedCandidates != null && (\forall int i; i >= 0 && i < rankedCandidates.length; rankedCandidates[i] != null)
	public Vote vote(List<PoliticalEntity> rankedCandidates) {
		Objects.requireNonNull(rankedCandidates);
		if(rankedCandidates.size() != candidates.size()) {
			throw new IllegalArgumentException("La dimensione della lista delle preferenze"
					+ " non coincide con il numero di candidati presenti nella votazione.");
		}
		for(PoliticalEntity e : rankedCandidates) {
			if(!candidates.contains(e)) throw new IllegalArgumentException("Il candidato " + e + " non e' valido per questa votazione.");
		}
		VoteOrdinale v = new VoteOrdinale(rankedCandidates);
		//addVote(v);
		return v;
	}
	
	/**
	 * Classe necessaria a rappresentare un voto della votazione di tipo PollOrdinale.
	 */
	public class VoteOrdinale implements Vote{
		private /*@ spec_public @*/ List<PoliticalEntity> rankedCandidates;
		
		//@ requires rankedCandidates != null;
		//@ ensures rankedCandidates.size == 0 || this.rankedCandidates == rankedCandidates;
		public VoteOrdinale(List<PoliticalEntity> rankedCandidates) {
			this.rankedCandidates = Objects.requireNonNull(rankedCandidates);
			if(this.rankedCandidates.size() == 0) {
				this.rankedCandidates.add(new Party("SCHEDA BIANCA"));
			}
		}
		
		//@ ensures \result == this.rankedCandidates;
		public List<PoliticalEntity> getPreference(){
			return rankedCandidates;
		}
		
		@Override
		public boolean equals(Object o) {
			if(o instanceof VoteOrdinale) {
				VoteOrdinale v = (VoteOrdinale) o;
				return rankedCandidates.equals(v.rankedCandidates);
			}
			return false;
		}
		
		@Override
		public String toString() {
			String str = "";
			if(rankedCandidates.size() == 0) {
				return "SCHEDA BIANCA";
			}
			for(int i=0 ; i < rankedCandidates.size() ; i++) {
				if(i==rankedCandidates.size()) return str += " " + rankedCandidates.get(i);
				str += " " + rankedCandidates.get(i) + ",";
			}
			return str;
		}
	}
	
}

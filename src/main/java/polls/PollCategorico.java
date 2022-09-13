package polls;

import java.sql.Timestamp;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import politics.Candidate;
import politics.Party;
import politics.PoliticalEntity;

public class PollCategorico extends Poll{
	/*@ invariant candidates != null && votes != null && (\forall int i; i >= 0 && i < candidates.length; candidates[i] != null) &&
	 @ (\forall int j; j >= 0 && j < votes.length; votes[j] != null) 
	 @*/
	private boolean absoluteMajority;
	private boolean withPreferences;
	private List<PoliticalEntity> candidates;
	private List<VoteCategorico> votes;
	
	public PollCategorico(String name, String description, Timestamp startDate, Timestamp endDate) {
		super(name, description, startDate, endDate);
		absoluteMajority = false;
		withPreferences = false;
		candidates = new ArrayList<PoliticalEntity>();
		votes = new ArrayList<VoteCategorico>();
	}
	
	public PollCategorico(String name, String description, Timestamp startDate, Timestamp endDate, boolean absoluteMajority, boolean withPreferences) {
		super(name, description, startDate, endDate);
		this.absoluteMajority = absoluteMajority;
		this.withPreferences = withPreferences;
		candidates = new ArrayList<PoliticalEntity>();
		votes = new ArrayList<VoteCategorico>();
	}
	
	public boolean getAbsoluteMajority() {
		return absoluteMajority;
	}
	
	public boolean getWithPreferences() {
		return withPreferences;
	}
	
	/**
	 * Restituisce una lista contenente tutte le entit� politiche candidate nella votazione this.
	 * @return Una lista di oggetti PoliticalEntity
	 */
	public List<PoliticalEntity> getAllCandidates() {
		return candidates;
	}
	
	/**
	 * Restituisce la lista dei partiti candidati nella votazione this.
	 * @return Una lista di oggetti Party
	 */
	public List<Party> getParties(){
		List<Party> party = new ArrayList<Party>();
		for(PoliticalEntity e : candidates) {
			if(e instanceof Party) {
				Party p = (Party) e;
				party.add(p);
			}
		}
		return party;
	}
	
	/**
	 * Restituisce una lista dei politici candidati nella votazione this.
	 * @return Una lista di oggetti Candidate
	 */
	public List<Candidate> getCandidates(){
		List<Candidate> cds = new ArrayList<Candidate>();
		for(PoliticalEntity e : cds) {
			if(e instanceof Candidate) {
				Candidate c = (Candidate) e;
				cds.add(c);
			}
		}
		return cds;
	}
	
	//@ requires v != null;
	/**
	 * Aggiunge alla lista di voti registrati il voto v fornito come argomento.
	 * @param v: un oggetto di tipo VoteCategorico
	 */
	public void addVote(VoteCategorico v) {
		Objects.requireNonNull(v);
		votes.add(v);
	}
	
	//@ requires e != null;
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
	
	//@ requires listOfCandidates != null && (\forall int i; i >= 0 && i < listOfCandidates.length; listOfCandidates[i] != null)
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
	
	//@ requires preferences != null && (\forall int i; i >= 0 && i < preferences.length; preferences[i] != null)
	public Vote vote(List<PoliticalEntity> preferences) {
		Objects.requireNonNull(preferences);
		VoteCategorico v = new VoteCategorico(preferences);
		if(!checkVoteValidity(v))
			throw new IllegalArgumentException("Not valid vote");
		return v;
	}
	
	
	/**
	 * Controlla che l'oggetto VoteCategorico v sia compatibile con la votazione this
	 * ovvero contenga un partito e dei candidati che sono indicati tra i candidati
	 * della votazione this.
	 * @param v: un oggetto di tipo VoteCategorico
	 * @return true se e' valido, false altrimenti
	 */
	private boolean checkVoteValidity(VoteCategorico v) {
		List<PoliticalEntity> pE = v.getPreference();
		
		if(!((pE.get(0)) instanceof Party))
			return false;
		
		if(((Party) pE.get(0)).getName().equals("SCHEDA BIANCA"))
			return true;
		
		boolean found = false;
		for(PoliticalEntity p1: pE) {
			for(PoliticalEntity p2: candidates) {
				if(p1 instanceof Party && p2 instanceof Party) {
					if(((Party) p1).equals((Party) p2)){
						found = true;
						break;
					}
				}else if(p1 instanceof Candidate && p2 instanceof Candidate) {
					if(((Candidate) p1).equals((Candidate) p2)){
						found = true;
						break;
					}
				}
			}
			if(!found)
				return false;
			found = false;
		}
		return true;
	}
	
	/**
	 * Le istanze di questa classe rappresentano un voto per la votazione di tipo
	 * PollCategorico. Sono caratterizzate da un oggetto di tipo Party che deve
	 * necessariamente essere diverso da null ed eventualmente da una lista di oggetti
	 * Candidate il cui partito per� deve combaciare con quello indicato dall'oggetto
	 * Party.
	 */
	public class VoteCategorico implements Vote{
		
		private Party party;
		private List<Candidate> candidates;
		
		public VoteCategorico(List<PoliticalEntity> politics) {
			Objects.requireNonNull(politics);
			this.party = null;
			candidates = new ArrayList<Candidate>();
			if(politics.size() == 0) {
				this.party = new Party("SCHEDA BIANCA");
			} else {
				for(int i = 0 ; i < politics.size() ; i++) {
					PoliticalEntity e = politics.get(i);
					if(e instanceof Party) {
						if(this.party == null) {
							this.party = (Party)e;
						} else {
							throw new IllegalArgumentException("Non puo' esserci piu' di un partito in un voto categorico.");
						}
					}
				}
				for(int i = 0 ; i < politics.size() ; i++) {
					PoliticalEntity e = politics.get(i);
					if(e instanceof Candidate) {
						Candidate c = (Candidate) politics.get(i);
						if(candidates.size() == 0) {
							candidates.add(c);
						} else {
							if(!candidates.get(i-1).getParty().equals(c.getParty())) {
								throw new IllegalArgumentException("Puoi inserire solo candidati dello stesso partito.");
							}
							candidates.add(c);
						}
					}
				}
			}
		}
		
		public List<PoliticalEntity> getPreference(){
			List<PoliticalEntity> preferences = new ArrayList<PoliticalEntity>();
			if(party != null) {
				preferences.add(party);
			}
			preferences.addAll(candidates);
			return preferences;
		}
		
		@Override
		public boolean equals(Object o) {
			if(o instanceof VoteCategorico) {
				VoteCategorico v = (VoteCategorico) o;
				if(party == null && v.party == null) {
					return candidates.equals(v.candidates);
				}
				return party.equals(v.party) && candidates.equals(v.candidates);
			}
			return false;
		}
		
		@Override
		public String toString() {
			String str = "" + party;
			for(int i=0 ; i < candidates.size() ; i++) {
				if(i == 0) str += " : ";
				if(i==candidates.size()) return str += " " + candidates.get(i);
				str += " " + candidates.get(i) + ",";
			}
			return str;
		}
	}

}

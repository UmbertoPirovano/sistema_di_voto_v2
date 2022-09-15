package polls;

import java.sql.Timestamp;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import politics.Party;
import politics.PoliticalEntity;

public class PollReferendum extends Poll {
	//@ invariant votes != null && (\forall int j; j >= 0 && j < votes.length; votes[j] != null);
	private /*@ spec_public @*/ boolean quorum;
	private /*@ spec_public @*/ List<VoteReferendum> votes;
	
	public PollReferendum(String name, String description, Timestamp startDate, Timestamp endDate) {
		super(name, description, startDate, endDate);
		this.quorum = false;
		votes = new ArrayList<VoteReferendum>();
	}
	
	//@ ensures this.quorum = quorum;
	public PollReferendum(String name, String description, Timestamp startDate, Timestamp endDate, boolean quorum) {
		super(name, description, startDate, endDate);
		this.quorum = quorum;
		votes = new ArrayList<VoteReferendum>();
	}
	
	//@ ensures \result == this.quorum;
	public boolean getQuorum() {
		return quorum;
	}
	
	//@requires v != null;
	//@ ensures (\exists int i; i >= 0 && i < votes.size(); votes(i) == v);
	public void addVote(VoteReferendum v) {
		Objects.requireNonNull(v);
		votes.add(v);
	}	
	
	//@ requires preferences != null && (\forall int i; i >= 0 && i < preferences.length; preferences[i] != null)
	public Vote vote(List<PoliticalEntity> preferences) {
		if(preferences.size() == 0) {
			return new VoteReferendum(null);	//Caso scheda bianca
		}else if(preferences.size() == 1) {
			Party party = (Party)preferences.get(0);
			if(party.getName().equals("Si'")) {
				return new VoteReferendum(true);
			} else {
				return new VoteReferendum(false);
			}
		} else {
			throw new IllegalArgumentException("Non e' possibile esprimere piu' di una preferenza.");
		}
	}	
	
	/**
	 * Oggetto necessario a rappresentare il voto per una votazione di tipo PollReferendum
	 */
	public class VoteReferendum implements Vote{
		private /*@ spec_public @*/ final Party choice;
		
		//@ ensures party != null;
		public VoteReferendum(Boolean value) {
			if(value == null) {
				this.choice = new Party("SCHEDA BIANCA");
			} else if(value) {
				this.choice = new Party("Si'");
			} else {
				this.choice = new Party("No");
			}
		}
		
		public List<PoliticalEntity> getPreference() {
			List<PoliticalEntity> preference = new ArrayList<PoliticalEntity>();
			preference.add(choice);
			return preference;
		}
		
		@Override
		public boolean equals(Object o) {
			if(o instanceof VoteReferendum) {
				VoteReferendum v = (VoteReferendum) o;
				return this.choice.equals(v.choice);
			}
			return false;
		}
		
		@Override
		public String toString() {
			return choice.getName();
		}
		
	}

}

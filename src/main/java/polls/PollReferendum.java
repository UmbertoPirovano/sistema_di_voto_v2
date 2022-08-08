package polls;

import java.sql.Timestamp;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import politics.Party;
import politics.PoliticalEntity;

public class PollReferendum extends Poll {
	
	private boolean quorum;
	private List<VoteReferendum> votes;
	
	public PollReferendum(String name, String description, Timestamp startDate, Timestamp endDate) {
		super(name, description, startDate, endDate);
		this.quorum = false;
		votes = new ArrayList<VoteReferendum>();
	}
	
	public PollReferendum(String name, String description, Timestamp startDate, Timestamp endDate, boolean quorum) {
		super(name, description, startDate, endDate);
		this.quorum = quorum;
		votes = new ArrayList<VoteReferendum>();
	}
	
	public boolean getQuorum() {
		return quorum;
	}
	
	public void addVote(VoteReferendum v) {
		Objects.requireNonNull(v);
		votes.add(v);
	}	
	
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
	
	@Override
	public String getResults() {
		int countYes = 0;
		int countTotal = 0;
		for(VoteReferendum v : votes) {
			if(v.choice.getName().equals("Si'")) countYes++;
			countTotal++;
		}		
		if(countTotal == 0) throw new IllegalArgumentException("Nessun voto conteggiato");
		int quorumQuote = (45000000/100*50)+1;
		if(quorum) {
			if(countTotal < quorumQuote) return "Quorum non raggiunto";
		}
		return "yes (" + countYes/countTotal*100 + "), no (" + (countTotal-countYes)/countTotal*100 + ")";		
	}
	
	
	/**
	 * Oggetto necessario a rappresentare il voto per una votazione di tipo PollReferendum
	 */
	public class VoteReferendum implements Vote{
		private final Party choice;
		
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

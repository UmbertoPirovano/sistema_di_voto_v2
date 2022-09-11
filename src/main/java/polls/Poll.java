package polls;

import java.sql.Timestamp;
import java.util.List;
import java.util.Objects;

import politics.PoliticalEntity;

public abstract class Poll {
	//@ invariant name != null && description != null && startDate != null && endDate != null;
	private final String name;
	private String description;
	private Timestamp startDate;
	private Timestamp endDate;
	
	//@ requires name != null && description != null && startDate != null && endDate != null;
	public Poll(String name, String description, Timestamp startDate, Timestamp endDate) {
		this.name = Objects.requireNonNull(name);
		this.description = Objects.requireNonNull(description);
		this.startDate = Objects.requireNonNull(startDate);
		this.endDate = Objects.requireNonNull(endDate);
		assert repOk();
	}
	
	private boolean repOk() {
		return startDate.before(endDate);
	}
	
	public String getName() {
		return name;
	}
	
	public String getDescription() {
		return description;
	}
	
	public Timestamp getStartDate() {
		return startDate;
	}
	
	public Timestamp getEndDate() {
		return endDate;
	}
	
	/**
	 * Istanzia e restituisce un oggetto di tipo Voto per la votazione this creato in base alla
	 * lista di PoliticalEntity fornita come argomento.
	 * @param preferences: La lista di PoliticalEntity scelte.
	 * @return Un'istanza di vote.
	 */
	public abstract Vote vote(List<PoliticalEntity> preferences);
	
	@Override
	public String toString() {
		return name;
	}
	
	@Override
	public boolean equals(Object o) {
		if(o instanceof Poll) {
			Poll p = (Poll) o;
			return name.equals(p.name) && description.equals(p.description)
					&& startDate.equals(p.startDate) && endDate.equals(p.endDate);
		}
		return false;
	}
}

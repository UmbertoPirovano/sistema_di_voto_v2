package politics;

import java.util.Objects;

public class Candidate implements PoliticalEntity{
	//@ invariant name != null && surname != null && party != null;
	private final String name;
	private final String surname;
	private /*@ spec_public @*/ Party party;
	
	//@ requires name != null && surname != null;
	public Candidate(String name, String surname) {
		this.name = Objects.requireNonNull(name);
		this.surname = Objects.requireNonNull(surname);
		this.party = null;
	}
	
	//@ requires name != null && surname != null && party != null;
	public Candidate(String name, String surname, Party party) {
		this.name = Objects.requireNonNull(name);
		this.surname = Objects.requireNonNull(surname);
		this.party = party;
	}
	
	public String getName() {
		return name;
	}
	
	public String getSurname() {
		return surname;
	}
	
	public Party getParty() {
		return party;
	}
	
	//@ requires p != null;
	//@ ensures party == p;
	public void setParty(Party p) {
		Objects.requireNonNull(p);
		this.party = p;
	}	
	
	@Override
	public String toString() {
		return this.name + " " + this.surname + " (" + this.party + ")";
	}
	
	@Override
	public boolean equals(Object o) {
		if(o instanceof Candidate) {
			Candidate c = (Candidate) o;
			return name.equals(c.name) && surname.equals(c.surname) && party.equals(c.party);
		}
		return false;
	}
}

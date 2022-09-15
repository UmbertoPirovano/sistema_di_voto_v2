package politics;

import java.util.Objects;

public class Party implements PoliticalEntity {
	//@ invariant name != null;
	private /*@ spec_public @*/ final String name;
	
	//@ require name != null;
	//@ ensures this.name == name;
	public Party(String name) {
		this.name = Objects.requireNonNull(name);
	}
	
	//@ ensures \result == name; 
	public String getName() {
		return name;
	}
	
	@Override
	public String toString() {
		return this.name;
	}
	
	@Override
	public boolean equals(Object o) {
		if(o instanceof Party) {
			Party p = (Party) o;
			return name.equals(p.name);
		}
		return false;
	}
}

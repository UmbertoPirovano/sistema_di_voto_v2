package politics;

import java.util.Objects;

public class Party implements PoliticalEntity {
	private final String name;
	
	public Party(String name) {
		this.name = Objects.requireNonNull(name);
	}
	
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

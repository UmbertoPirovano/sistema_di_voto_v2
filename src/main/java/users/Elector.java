/**
 * Le istanze di questa classe rappresentano un elettore per la piattaforma di voto online.
 * Estende la classe User e il parametro 'username' deve combaciare con il codice fiscale della
 * persona per la quale viene creata l'istanza di questo oggetto.
 */
package users;

import java.util.Objects;

public class Elector extends User {
	private final String name;
	private final String surname;
	
	public Elector(String username, String password, String name, String surname) {
		super(username, password);
		this.name = Objects.requireNonNull(name);
		this.surname = Objects.requireNonNull(surname);
		assert validateFiscalCode(username, name, surname);
	}
	
	public String getName() {
		return name;
	}
	
	public String getSurname() {
		return surname;
	}
	
	/**
	 * Controlla che l'argomento 'username' combaci con un valido codice fiscale per
	 * l'elettore this.
	 * @param username
	 * @return
	 */
	private boolean validateFiscalCode(String username, String name, String surname) {
		//TODO: controllare che il codice fiscale sia valido
		return true;
	}
	
	@Override
	public boolean equals(Object o) {
		if(o instanceof Elector) {
			Elector e = (Elector) o;
			return name.equals(e.name) && surname.equals(e.surname) 
					&& this.getUsername().equals(e.getUsername()); 
		}
		return false;
	}

}

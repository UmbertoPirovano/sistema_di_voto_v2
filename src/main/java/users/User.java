/**
 * Questa classe astratta rappresenta un utente del sistema. L'utente è caratterizzato
 * da uno username ed una password.
 */
package users;

import java.util.Objects;

public abstract class User {
	private final String username;
	private String password;
	
	public User(String username, String password) {
		this.username = Objects.requireNonNull(username);
		this.password = Objects.requireNonNull(password);
	}
	
	public String getUsername() {
		return username;
	}
	
	/**
	 * Controlla che la stringa fornita in argomento corrisponda con la password
	 * usata da this.
	 * @param pwd
	 * @return True se la password è corretta, False altrimenti.
	 */
	private boolean checkPassword(String pwd) {
		Objects.requireNonNull(pwd);
		return this.password.equals(pwd);
	}
	
	/**
	 * Metodo che permette di cambiare la password associata all'utente this.
	 * @param oldPassword La password attualmente in uso
	 * @param newPassword La nuova password
	 * @throws IllegalArgumentException se oldPassword non corrisponde con la password attualmente in uso da this.
	 */
	public void changePassword(String oldPassword, String newPassword) {
		Objects.requireNonNull(oldPassword);
		Objects.requireNonNull(newPassword);
		if(!checkPassword(oldPassword)) 
			throw new IllegalArgumentException("Password errata");
		this.password = newPassword;
	}
	
	@Override
	public boolean equals(Object o) {
		if(o instanceof User) {
			User y = (User) o;
			return this.username.equals(y.username) && this.password.equals(y.password);
		}
		return false;
	}
	
	@Override
	public String toString() {
		return username;
	}
}

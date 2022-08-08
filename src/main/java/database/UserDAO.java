package database;

import java.util.List;
import users.User;

public interface UserDAO {
	
	/**
	 * Restituisce una lista di User contenente tutti gli utenti registrati nel sistema.
	 * @return Una lista di oggetti di tipo User.
	 */
	public List<User> getAll();
	
	/**
	 * Restituisce uno specifico oggetto User che corrisponde all'utente definito da 'username'.
	 * @param username: lo username dell'utente
	 * @return Un'istanza di User
	 */
	public User getUser(String username);
	
	/**
	 * Registra l'utente rappresentato dall'oggetto User u se esso non è già presente.
	 * @param u: un oggetto di tipo User
	 * @param password: la password scelta per l'utente u
	 */
	public void addUser(User u, String password);
	
	/**
	 * Elimina dal database l'utente u.
	 * @param u: l'oggetto User che rappresenta l'utente da eliminare.
	 */
	public void deleteUser(User u);
	
	/**
	 * Restituisce true se le credenziali inserite sono corrette, false altrimenti.
	 * @param username: lo username dell'utente
	 * @param password: la password dell'utente
	 * @return Un valore booleano.
	 */
	public boolean checkCredentials(String username, String password);
	
	/**
	 * Restituisce l'utente registrato nel sistema e definito da 'username'
	 * @param username: lo username dell'utente
	 * @param password: la password dell'utente
	 * @return Un'istanza di User che rappresenta l'utente identificato da username+password.
	 */
	public User login(String username, String password);
	
}

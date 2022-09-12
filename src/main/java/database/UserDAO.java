package database;

import java.util.List;

import polls.Poll;
import users.Administrator;
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
	 * Registra l'utente rappresentato dall'oggetto User u se esso non � gi� presente.
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
	
	/**
	 * Invia al database le informazioni necessarie a creare una nuova entry di login o logout per la tabella dei log.
	 * @param user Un utente del sistema.
	 * @param azione Una breve descrizione dell'azione svolta da user.
	 */
	public void addLogEntry(User user, String azione);
	
	/**
	 * Invia al database le informazioni necessarie a creare una nuova entry di gestione di un utente per la tabella dei log.
	 * @param user Un amministratore del sistema.
	 * @param azione Una breve descrizione dell'azione svolta da user.
	 * @param other L'utente che viene gestito da user.
	 */
	public void addLogEntry(Administrator user, String azione, User other);
	
	/**
	 * Invia al database le informazioni necessarie a creare una nuova entry di interazione con una votazione per la tabella dei log.
	 * @param user Un utente del sistema.
	 * @param azione Una breve descrizione dell'azione svolta da user.
	 * @param p La votazione con cui interagisce user.
	 */
	public void addLogEntry(User user, String azione, Poll p);
	
	/**
	 * Restituisce una lista di stringhe contenenti i primi dieci log log reperiti dal database. I log vengono ordinati in ordine decrescente
	 * rispetto al loro timestamp.
	 * @return La lista di stringhe log.
	 */
	public List<String> getLog();
}

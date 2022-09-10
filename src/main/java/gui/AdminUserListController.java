package gui;

import java.io.IOException;
import java.net.URL;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.ResourceBundle;

import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.scene.input.MouseEvent;
import javafx.scene.text.Text;
import javafx.stage.Stage;
import polls.Poll;
import system.SystemEvote;
import system.SystemEvoteObserver;
import users.Administrator;
import users.User;

public class AdminUserListController implements Initializable, SystemEvoteObserver {
	
	private List<User> users;
	
    @FXML
    private Button addUserButton;

    @FXML
    private Button backButton;

    @FXML
    private TableColumn<RowUser, String> col_username;
    
    @FXML
    private TableColumn<RowUser, String> col_name;

    @FXML
    private TableColumn<RowUser, String> col_surname;
    
    @FXML
    private TableColumn<RowUser, String> col_type;
    
    @FXML
    private TableColumn<RowUser, String> col_status;

    @FXML
    private TableColumn<RowUser, ButtonBar> col_action;

    @FXML
    private Button logoutButton;

    @FXML
    private Text nameSurnameLabel;

    @FXML
    private TableView<RowUser> userTable;

    @FXML
    private Text usernameLabel;

    @FXML
    void goBack(ActionEvent event) {
    	SystemEvote.getInstance().removeObserver(this);
    	try {
			logoutButton.getScene().getWindow().hide();
    		Parent root = FXMLLoader.load(getClass().getResource("AdminMenu.fxml"));
            Stage stage = new Stage();
        	stage.setTitle("Sistema di voto elettronico - Menù amministratore");
        	stage.setScene(new Scene(root, 900, 700));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			System.out.println(e.getMessage());
		}
    }

    @FXML
    void logout(ActionEvent event) {
    	SystemEvote.getInstance().removeObserver(this);
    	SystemEvote.getInstance().logout();
    	showLoginWindow();
    }

    @FXML
    void mouse(MouseEvent event) {

    }

    @FXML
    void showUserEditor(ActionEvent event) {
    	try {
    		Parent root = FXMLLoader.load(getClass().getResource("AdminUserSelectType.fxml"));
            Stage stage = new Stage();
        	stage.setTitle("Sistema di voto elettronico - User editor");
        	stage.setScene(new Scene(root, 500, 400));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			System.out.println(e.getMessage());
		}
    }

	@Override
	public void initialize(URL location, ResourceBundle resources) {
		SystemEvote.getInstance().addObserver(this);
		Administrator a = (Administrator) SystemEvote.getInstance().getSession().getUser();
		nameSurnameLabel.setText(a.getUsername());
		usernameLabel.setText("");
		//Associare le colonne agli attributi
		col_username.setCellValueFactory(new PropertyValueFactory<>("Username"));
    	col_name.setCellValueFactory(new PropertyValueFactory<>("Name"));
    	col_surname.setCellValueFactory(new PropertyValueFactory<>("Surname"));
    	col_type.setCellValueFactory(new PropertyValueFactory<>("Type"));
    	col_action.setCellValueFactory(new PropertyValueFactory<>("ButtonBar"));
	}

	@Override
	public void update(List<User> users, List<Poll> polls) {
		Objects.requireNonNull(users);
		this.users = users;
		System.out.println("Local user list updated. Size: " + this.users.size());
		refreshList();		
	}
	
	/**
	 * Aggiorna gli elementi mostrati nella tabella.
	 */
	private void refreshList() {
		userTable.getItems().clear();    	
    	for(User u : users) {
    		RowUser ru = new RowUser(u);
    		userTable.getItems().add(ru);
    	}		
    	Collections.sort(userTable.getItems());
	}
	
	/**
	 * Chiude la schermata corrente ed apre la schermata di login
	 */
	private void showLoginWindow() {
		try {
			logoutButton.getScene().getWindow().hide();
    		Parent root = FXMLLoader.load(getClass().getResource("LoginWindow.fxml"));
            Stage stage = new Stage();
        	stage.setTitle("Sistema di voto elettronico - Login");
        	stage.setScene(new Scene(root, 500, 390));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			System.out.println(e.getMessage());
		}
	}
}
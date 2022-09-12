package gui;

import java.io.IOException;
import java.net.URL;
import java.util.ResourceBundle;

import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.text.Text;
import javafx.stage.Stage;
import system.SystemEvote;
import users.Administrator;

public class AdminMenuController implements Initializable {
	
	@FXML
	private Button logBtn;
	
    @FXML
    private Button logoutButton;

    @FXML
    private Text nameSurnameLabel;

    @FXML
    private Text usernameLabel;
    
    @FXML
    private Button pollButton;

    @FXML
    private Button userButton;

    @FXML
    void logout(ActionEvent event) {
    	SystemEvote.getInstance().logout();
    	showLoginWindow();
    }

    @FXML
    void showPollListAdmin(ActionEvent event) {
    	try {
			logoutButton.getScene().getWindow().hide();
    		Parent root = FXMLLoader.load(getClass().getResource("AdminPollList.fxml"));
            Stage stage = new Stage();
        	stage.setTitle("Sistema di voto elettronico - Gestione votazioni (admin)");
        	stage.setScene(new Scene(root, 900, 700));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			System.out.println(e.getMessage());
		}
    }

    @FXML
    void showUserListAdmin(ActionEvent event) {
    	try {
			logoutButton.getScene().getWindow().hide();
    		Parent root = FXMLLoader.load(getClass().getResource("AdminUserList.fxml"));
            Stage stage = new Stage();
        	stage.setTitle("Sistema di voto elettronico - Gestione utenti (admin)");
        	stage.setScene(new Scene(root, 900, 700));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			System.out.println(e.getMessage());
		}
    }    

	@Override
	public void initialize(URL location, ResourceBundle resources) {
		Administrator a = (Administrator) SystemEvote.getInstance().getSession().getUser();
		nameSurnameLabel.setText(a.getUsername());
		usernameLabel.setText("");		
	}
	
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
	
	@FXML
    void showLogWindow(ActionEvent event) {
		try {
			logoutButton.getScene().getWindow().hide();
    		Parent root = FXMLLoader.load(getClass().getResource("AdminLogList.fxml"));
            Stage stage = new Stage();
        	stage.setTitle("Sistema di voto elettronico - Lista dei log");
        	stage.setScene(new Scene(root, 900, 700));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			System.out.println(e.getMessage());
		}
    }
}
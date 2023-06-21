//
//  SearchBar.swift
//  AddressGeocoding
//
//  Created by Nom4D on 20/03/2023.
//

import SwiftUI

struct SearchBar : UIViewRepresentable {
    @Binding var text : String

    class Cordinator : NSObject, UISearchBarDelegate {
        @Binding var text : String

        init(text : Binding<String>) {
            _text = text
        }

        func searchBar(_ searchBar: UISearchBar, textDidChange searchText: String) {
            text = searchText
        }
        
        func searchBarSearchButtonClicked(_ searchBar: UISearchBar) {
            searchBar.endEditing(true)
            searchBar.resignFirstResponder()
        }

        func searchBarCancelButtonClicked(_ searchBar: UISearchBar) {
            searchBar.endEditing(true)
            searchBar.resignFirstResponder()
        }
    }

    func makeCoordinator() -> SearchBar.Cordinator {
        return Cordinator(text: $text)
    }

    func makeUIView(context: UIViewRepresentableContext<SearchBar>) -> UISearchBar {
        let searchBar = UISearchBar(frame: .zero)
        searchBar.placeholder = "6969 Cool St, Weedsport, NY 13166"
        searchBar.barStyle = .default
        searchBar.delegate = context.coordinator
        return searchBar
    }

    func updateUIView(_ uiView: UISearchBar, context: UIViewRepresentableContext<SearchBar>) {
        uiView.text = text
        uiView.showsCancelButton = uiView.text!.count > 0 ? true : false
    }
}

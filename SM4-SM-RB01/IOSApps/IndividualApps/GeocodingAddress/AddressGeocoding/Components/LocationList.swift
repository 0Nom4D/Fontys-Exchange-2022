//
//  LocationList.swift
//  AddressGeocoding
//
//  Created by Nom4D on 28/03/2023.
//

import SwiftUI

struct LocationList: View {
    @EnvironmentObject private var geocoderHandler: GeocoderHandler

    @Binding var offset: CGFloat

    var sectionName: String?
    var elementList: [EnumeratedSequence<[Location]>.Element]

    @State private var chosenLocation: UUID?

    var elementsList: some View {
        List(elementList, id: \.1.id, selection: $chosenLocation) { (_, item) in
            Text("\(item.name), \(item.additionalName)")
                .onTapGesture {
                    geocoderHandler.isDetailed = true
                    if item.coordinates == nil {
                        geocoderHandler.findLocation(location: item)
                    } else {
                        geocoderHandler.currentLocation = item
                    }
                }
        }
        .listStyle(.inset)
    }

    var body: some View {
        if sectionName != nil {
            Section(header: HStack(alignment: .top) {
                Text(sectionName!).sectionHeaderStyle()
                Spacer()
            }) {
                elementsList
                    .frame(height: UIScreen.main.bounds.height - (offset + 120))
            }
        } else {
            elementsList
                .frame(height: UIScreen.main.bounds.height - (offset + 90))
        }
    }
}

public extension Text {
    func sectionHeaderStyle() -> some View {
        self
            .font(.system(.title3))
            .padding(.leading, 10)
            .fontWeight(.heavy)
            .foregroundColor(.primary)
            .textCase(nil)
    }
}
